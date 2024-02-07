/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.random_oracle
import computational_monads.simulation_semantics.constructions.logging_oracle
import computational_monads.simulation_semantics.constructions.identity_oracle
import computational_monads.simulation_semantics.oracle_append
import crypto_foundations.sec_experiment

/-!
# Cryptographic Signature Schemes

This file defines signature algorithms and security properties for them.
Signature algorithms are defined by a structure containing the relevant types,
and algorithms with inputs and outputs corresponding to the provided types.
A signature scheme is then defined to be a set of signatures indexed by a security parameter

Completeness is defined to be the property that any result of gen and sign passes verify.
Note that this doesn't allow for negligable failure, as some literature does.

Unforgeable is defined to be the property that any adversary with access to a signing oracle
cannot forge a valid message/signature pair with more than negligable advantage.

Note that the schemes assume algorithms have access to a shared random oracle.
Signature schemes that don't need this can provide the empty spec `∅`,
  which has no way to actually be queried
-/

open_locale ennreal big_operators
open oracle_comp oracle_spec prod

/-- A `signature_alg spec M PK SK S` is an algorithm for signing messages,
where signatures are on messages in `M`, public and secret keys are in `PK` and `SK`,
and final signatures are of type `S`. -/
structure signature_alg (spec : oracle_spec) (M PK SK S : Type)
  extends oracle_algorithm spec :=
(keygen : unit → oracle_comp spec (PK × SK))
(sign : (PK × SK) × M → oracle_comp spec S)
(verify : PK × M × S → oracle_comp spec bool)

namespace signature_alg

variables {spec : oracle_spec} {M PK SK S : Type}

section sound

/-- Experiment for checking that a signature algorithm is sound.
Given a message `m`, input generation just generates a public/secret key pair,
and the main experiment signs and verifies the message with the generated keys.
For a sound signature algorithm this will always succeed. -/
def soundness_exp (sig : signature_alg spec M PK SK S) (m : M) :
  sec_exp spec (PK × SK) bool :=
{ inp_gen := sig.keygen (),
  main := λ ⟨pk, sk⟩,
    do {σ ← sig.sign ((pk, sk), m),
      sig.verify (pk, m, σ) },
  is_valid := λ ks b, b = tt,
  .. sig }

namespace soundness_exp

variables (sig : signature_alg spec M PK SK S) (m : M)

@[simp] lemma to_oracle_algorithm_eq :
  (soundness_exp sig m).to_oracle_algorithm = sig.to_oracle_algorithm := rfl

@[simp] lemma inp_gen_eq : (soundness_exp sig m).inp_gen = sig.keygen () := rfl

@[simp] lemma main_eq (ks : PK × SK) : (soundness_exp sig m).main ks =
  do {σ ← sig.sign (ks, m), sig.verify (ks.1, m, σ)} := prod.rec_on ks (λ _ _, rfl)

@[simp] lemma is_valid_iff (ks : PK × SK) (b : bool) :
  (soundness_exp sig m).is_valid ks b ↔ b = tt := iff.rfl

@[simp] lemma run_eq : (soundness_exp sig m).run =
  sig.exec (do {ks ← sig.keygen (), σ ← sig.sign (ks, m),
    b ← sig.verify (ks.1, m, σ), return (ks, b)}) :=
by simp_rw [sec_exp.run_def, to_oracle_algorithm_eq, inp_gen_eq, main_eq, bind_assoc]

/-- Explicitly express the advantage of `soundness_exp` in terms of `prob_output`. -/
lemma advantage_eq (sig : signature_alg spec M PK SK S) (m : M) :
  (soundness_exp sig m).advantage = ⁅= tt | sig.exec (do {ks ← sig.keygen (),
    σ ← sig.sign (ks, m), sig.verify (ks.1, m, σ)})⁆ :=
by simp [sec_exp.advantage_eq_prob_event, simulate'.def]

end soundness_exp

/-- A signature algorithm is complete if all messages are valid. -/
def is_sound (sig : signature_alg spec M PK SK S) : Prop :=
∀ m, (soundness_exp sig m).advantage = 1

lemma is_sound_iff_forall_message (sig : signature_alg spec M PK SK S) :
  sig.is_sound ↔ ∀ m, (soundness_exp sig m).advantage = 1 := iff.rfl

end sound

/-- Simulate a computation with access to a `signing_oracle_spec` to one with `base_oracle_spec`,
using the provided public / secret keys to answer queries for signatures.
Additionally tracks responses to queries, returing the resulting `query_cache`,
which can be used to check that the adversary hadn't gotten a signature for their final output. -/
def signing_sim_oracle (sig : signature_alg spec M PK SK S) (pk : PK) (sk : SK)
  [inhabited S] [fintype S] [decidable_eq M] [decidable_eq S] :
  sim_oracle (spec ++ (M ↦ₒ S)) spec (M ↦ₒ S).query_log :=
let so' : sim_oracle (M ↦ₒ S) spec punit :=
  λ _ m, do {σ ← sig.sign ((pk, sk), m.1), return (σ, ())} in
(idₛₒ ++ₛₒ ((so' ∘ₛₒ loggingₛₒ).mask_state
  (equiv.prod_punit _))).mask_state (equiv.punit_prod _)

alias signing_sim_oracle ← signingₛₒ

section unforgeable

variables [inhabited S] [fintype S] [decidable_eq M] [decidable_eq S]

@[inline, reducible] def unforgeable_adv_spec (sig : signature_alg spec M PK SK S) :
  oracle_spec := spec ++ (M ↦ₒ S)

/-- An adversary for the unforgeable signature experiment.
  Note that the adversary only has access to the public key. -/
-- structure unforgeable_adversary (sig : signature) extends
--   sec_adversary (unif_spec ++ sig.random_spec ++ sig.signing_spec) sig.PK (sig.M × sig.S)
def unforgeable_adv (sig : signature_alg spec M PK SK S) :=
sec_adv (spec ++ (M ↦ₒ S)) PK (M × S)

namespace unforgeable_adversary

-- variables {sig : signature} (adversary : unforgeable_adversary sig)

-- /-- Wrapper function for simulation that hides the "state values" of the stateless oracles.
-- Runs the adversary with a signing oracle based on the provided public/secret keys,
-- returning the results of the adversary, and a log of the queries made by the adversary -/
-- def simulate_signing_oracle (pk : sig.PK) (sk : sig.SK) :
--   oracle_comp (unif_spec ++ sig.random_spec)
--     ((sig.M × sig.S) × (sig.M ↦ₒ sig.S).query_cache) :=
-- (prod.map id prod.snd) <$> (dsimulate (idₛₒ ++ₛₒ sig.signingₛₒ pk sk) (adversary.run pk))

end unforgeable_adversary

/-- Experiment for unforgeability of a signature algorithm. -/
def unforgeable_exp {sig : signature_alg spec M PK SK S}
  (adv : unforgeable_adv sig) : sec_exp spec (PK × SK) bool :=
{ inp_gen := sig.keygen (),
  main := λ ⟨pk, sk⟩, do
    { ⟨⟨m, σ⟩, log⟩ ← simulate (sig.signingₛₒ pk sk) (adv.run pk) ∅,
      b ← sig.verify (pk, m, σ),
      return (b && !(log.was_queried () m)) },
  is_valid := λ _ b, b = tt,
  .. sig } -- Same simulation oracles as the signature itself. 

namespace unforgeable_exp

variables {sig : signature_alg spec M PK SK S} (adv : unforgeable_adv sig)

@[simp] lemma inp_gen_eq : (unforgeable_exp adv).inp_gen = sig.keygen () := rfl

@[simp] lemma main_apply (ks : PK × SK) : (unforgeable_exp adv).main ks = do
  { z ← simulate (sig.signingₛₒ ks.1 ks.2) (adv.run ks.1) ∅,
    b ← sig.verify (ks.1, z.1.1, z.1.2),
    return (b && !(z.2.was_queried () z.1.1)) } :=
begin
  cases ks,
  simp [unforgeable_exp],
  congr' 1,
  ext z,
  rcases z with ⟨⟨m, σ⟩, log⟩,
  simp [unforgeable_exp],
end

@[simp] lemma is_valid_eq (ks : PK × SK) :
  (unforgeable_exp adv).is_valid ks = (= tt) := funext (λ b, rfl)

@[simp] lemma is_valid_iff (ks : PK × SK) (b : bool) :
  (unforgeable_exp adv).is_valid ks b ↔ b = tt := iff.rfl

@[simp] lemma to_oracle_algorithm_eq : (unforgeable_exp adv).to_oracle_algorithm =
  sig.to_oracle_algorithm := rfl

/-- TODO: lemmas like this are always gross to prove, from pattern matching stuff -/
lemma advantage_eq_prob_output : (unforgeable_exp adv).advantage =
  ⁅= tt | sig.exec (do {⟨pk, sk⟩ ← sig.keygen (),
    ⟨⟨m, σ⟩, log⟩ ← simulate (sig.signingₛₒ pk sk) (adv.run pk) ∅,
    b ← sig.verify (pk, m, σ),
    return (b && !(log.was_queried () m))})⁆ :=
begin
  rw [sec_exp.advantage_eq_prob_event],
  simp_rw [is_valid_eq, prob_event_eq_eq_prob_output_map],
  congr' 1,
  simp only [oracle_algorithm.exec_bind, map_bind, sec_exp.run, main_apply, inp_gen_eq,
    to_oracle_algorithm_eq, mk.eta, simulate'_bind, simulate_bind, simulate_return,
    simulate'_return, map_pure, oracle_comp.pure_eq_return],
  congr' 2,
  ext z,
  congr' 1,
  rcases z with ⟨⟨m, σ⟩, log⟩,
  simp only [simulate_bind],
  congr' 1,
  ext z',
  rcases z' with ⟨⟨⟨m, σ⟩, log⟩, u⟩,
  simp only [simulate_bind, simulate_return]
end

end unforgeable_exp

-- noncomputable def unforgeable_advantage (sig : signature)
--   (adv : unforgeable_adversary sig) : ℝ≥0∞ :=
-- adv.advantage sig.unforgeable_experiment

end unforgeable

end signature_alg

-- /-- signature scheme is a set of signature algorithms indexed by a security parameter -/
-- def signature_scheme (spec : ℕ → oracle_spec) (M PK SK S : ℕ → Type) :=
-- Π (sp : ℕ), signature_alg (spec sp) (M sp) (PK sp) (SK sp) (S sp)

-- namespace signature_scheme

-- open signature_alg

-- d

-- /-- Scheme is complete if it is complete for each security parameter -/
-- def complete (sig_scheme : signature_scheme) : Prop :=
-- ∀ (sp : ℕ), (sig_scheme sp).complete

-- /-- Signature scheme is unforgeable if any polynomial time adversary has negligible advantage in
--   `unforgeable_experiment` as the security parameter grows -/
-- def unforgeable (sig_scheme : signature_scheme) : Prop :=
-- ∀ (adv : Π (sp : ℕ), unforgeable_adversary $ sig_scheme sp),
--   negligable (λ sp, (adv sp).advantage (sig_scheme sp).unforgeable_experiment)

-- end signature_scheme