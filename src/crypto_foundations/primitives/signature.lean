/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.random_oracle
import computational_monads.simulation_semantics.constructions.logging_oracle
import computational_monads.simulation_semantics.constructions.identity_oracle
import computational_monads.simulation_semantics.oracle_append
import crypto_foundations.sec_adversary

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
Signature schemes that don't need this can provide the empty spec `[]ₒ`,
  which has no way to actually be queried
-/

open_locale ennreal big_operators
open oracle_comp oracle_spec prod

/-- Signature on messages `M`, public and secret keys `PK` and `SK`, signatures of type `S`.
  We model the algorithms as having access to a uniform selection oracle,
    and a set of random oracles that the algorithm has access to.
  If not in the random oracle model, can just take `random_oracles := []ₒ`, the empty `oracle_spec`
  We also bundle the polynomial complexity of the algorithms into the structure. -/
structure signature := -- TODO: signature_alg?
-- Types of the possible messages, public keys, secret keys, and signatures
(M PK SK S : Type)
-- Equality between messages and between signatures is decidable (unneeded for `PK` and `SK`)
(decidable_eq_M : decidable_eq M) (decidable_eq_S : decidable_eq S)
-- There exists finitely many (but not-zero) possible signatures
(inhabited_S : inhabited S) (fintype_S : fintype S)
-- Set of random oracles available to the signature algorithms
(random_spec : oracle_spec)
-- The actual algorithms of the signature scheme.
(gen : unit → oracle_comp (uniform_selecting ++ random_spec) (PK × SK))
(sign : PK × SK × M → oracle_comp (uniform_selecting ++ random_spec) S)
(verify : PK × M × S → oracle_comp (uniform_selecting ++ random_spec) bool)

namespace signature

-- Add type-class instances of the type classes bundled into a signature algorithm.
instance decidable_eq_S' (sig : signature) : decidable_eq sig.S := sig.decidable_eq_S
instance decidable_eq_M' (sig : signature) : decidable_eq sig.M := sig.decidable_eq_M
instance inhabited_S' (sig : signature) : inhabited sig.S := sig.inhabited_S
instance fintype_S' (sig : signature) : fintype sig.S := sig.fintype_S

/-- Shorthand for the combination of the uniform selection and random oracles,
exactly the oracles available to the signature algorithms themselves -/
@[reducible, inline] def base_spec (sig : signature) := uniform_selecting ++ sig.random_spec

/-- A signing oracle corresponding to a given signature scheme -/
@[reducible, inline] def signing_spec (sig : signature) [inhabited sig.S] := sig.M ↦ₒ sig.S

/-- Simulate the basic oracles for the signature, using `random_oracle` to simulate the
random oracle and preserving the `uniform_selecting` oracle as is. -/
noncomputable def baseₛₒ (sig : signature) :
  sim_oracle sig.base_spec uniform_selecting (sig.random_spec.query_cache) :=
sim_oracle.mask_state (idₛₒ ++ₛ randomₛₒ)
  (equiv.punit_prod sig.random_spec.query_cache)

/-- Simulate a computation with access to a `signing_oracle_spec` to one with `base_oracle_spec`,
using the provided public/secret keys to answer queries for signatures.
Additionally uses `cachingₛₒ` to respond to queries, returing the resulting `query_cache`,
which can be used to check that the adversary hadn't gotten a signature for their final output. -/
def signingₛₒ (sig : signature) (pk : sig.PK) (sk : sig.SK) :
  sim_oracle sig.signing_spec sig.base_spec (sig.M ↦ₒ sig.S).query_cache :=
sim_oracle.mask_state (⟪λ _ m, sig.sign (pk, sk, m)⟫ ∘ₛ cachingₛₒ)
  (equiv.prod_punit (signing_spec sig).query_cache)

section simulate_random_oracle

/-- Run `sig.simulate` with a random oracle for `random_spec`.
Allow for any initial random  oracle cache, usually it will be empty before any other queries.
This is assumed to be the "correct" way to generate a key, at least for security property. -/
noncomputable def simulate_gen (sig : signature) (cache : sig.random_spec.query_cache) :
  oracle_comp uniform_selecting ((sig.PK × sig.SK) × sig.random_spec.query_cache) :=
simulate sig.baseₛₒ (sig.gen ()) cache

/-- Run the signing algorithm using a random oracle initialized to `cache`.
This is assumed to be the "correct" way to sign a message, at least for security properties. -/
noncomputable def simulate_sign (sig : signature) (cache : sig.random_spec.query_cache)
  (pk : sig.PK) (sk : sig.SK) (m : sig.M) :
  oracle_comp uniform_selecting (sig.S × sig.random_spec.query_cache) :=
simulate sig.baseₛₒ (sig.sign (pk, sk, m)) cache

/-- Run the verification algorithm using a random oracle initialized to `cache`.
This is assumed to be the "correct" way to verify signatures, at least for security properties. -/
noncomputable def simulate_verify (sig : signature) (cache : sig.random_spec.query_cache)
  (pk : sig.PK) (m : sig.M) (σ : sig.S) :
  oracle_comp uniform_selecting (bool × sig.random_spec.query_cache)  :=
simulate sig.baseₛₒ (sig.verify (pk, m, σ)) cache

variables (sig : signature) (cache : sig.random_spec.query_cache)

end simulate_random_oracle

section completeness_experiment

/-- Generate a key, sign on the given message, and return the result of verify on the signature.
Random oracles have a shared cache for the entire computation,
and the uniform selection oracle just forwards its query on. -/
noncomputable def completeness_experiment (sig : signature) (m : sig.M) :
  oracle_comp uniform_selecting bool := default_simulate' sig.baseₛₒ
    (do {ks ← sig.gen (), σ ← sig.sign (ks.1, ks.2, m), sig.verify (ks.1, m, σ)})

-- lemma completeness_experiment_dist_equiv (sig : signature) (m : sig.M) :
--   sig.completeness_experiment m ≃ₚ
--     do {((pk, sk), cache₀) ← sig.simulate_gen,
--       (σ, cache₁) ← sig.simulate_sign cache₀ (pk, sk, m),
--       (b, cache₂) ← sig.simulate_verify cache₁ (pk, m, σ),
--       return b } :=
-- begin
--   sorry,
-- end

end completeness_experiment

section is_valid

/-- A signature  is valid for `sig` if it is always verified by `sig.verify`.
This definition is based on the assumption that valid signatures are always accepted.
If the signature has a potential chance of failure then it isn't really meaningful. -/
def is_valid (sig : signature) (pk : sig.PK) (m : sig.M) (σ : sig.S)
  (cache : sig.random_spec.query_cache) : Prop :=
fst '' (sig.simulate_verify cache pk m σ).support = {tt}

variables (sig : signature) (pk : sig.PK) (m : sig.M) (σ : sig.S)
  (cache : sig.random_spec.query_cache)

lemma is_valid.def : sig.is_valid pk m σ cache =
  (fst '' (sig.simulate_verify cache pk m σ).support = {tt}) := rfl

lemma is_valid_iff_prob_output : sig.is_valid pk m σ cache ↔
  ⁅= tt | fst <$> sig.simulate_verify cache pk m σ⁆ = 1 :=
by rw [prob_output_eq_one_iff, is_valid.def, support_map]

end is_valid

section complete

/-- Signature is complete if for any possible message, the generated signature is valid,
i.e. the output of `sign` always returns true when `verify` is called.
note that this definition doesn't allow for negligable failure of signing -/
def complete (sig : signature) := ∀ (m : sig.M), ⁅= tt | completeness_experiment sig m⁆ = 1

lemma complete_iff_forall_is_valid (sig : signature) : sig.complete ↔
  (∀ m : sig.M, ∀ gen_z ∈ (sig.simulate_gen ∅).support,
    ∀ sig_z ∈ (sig.simulate_sign (snd gen_z) (fst (fst gen_z)) (snd (fst gen_z)) m).support,
      sig.is_valid gen_z.1.1 m (fst sig_z) sig_z.2) :=
sorry

variable (sig : signature)

-- lemma completeness_experiment.def (m : sig.M) : sig.completeness_experiment m = default_simulate'
--   sig.baseₛₒ (do {k ← sig.gen (), σ ← sig.sign (k.1, k.2, m), sig.verify (k.1, m, σ)}) :=
-- begin
--   rw [completeness_experiment],
--   congr,
--   refine funext (λ x, _),
--   cases x,
--   simp [completeness_experiment._match_1],
-- end

-- /-- The possible outputs of running the completeness experiment,
--   as a union over the keys and signature generated, plus internal random oracle caches. -/
-- @[simp] lemma support_completeness_experiment (m : sig.M) :
--   (completeness_experiment sig m).support = ⋃ (pk : sig.PK) (sk : sig.SK) (σ : sig.S)
--     (cache cache' : sig.random_spec.query_cache)
--     (hk : ((pk, sk), cache) ∈ (default_simulate sig.baseₛₒ $ sig.gen ()).support)
--     (hσ : (σ, cache') ∈ (simulate sig.baseₛₒ (sig.sign (pk, sk, m)) cache).support),
--       (simulate' sig.baseₛₒ (sig.verify (pk, m, σ)) cache').support :=
-- begin
--   ext x,
--   simp only [completeness_experiment.def, default_simulate',
--     support_simulate'_bind, set.mem_Union],
--   sorry,
-- end

-- lemma complete_iff_signatures_support_subset :
--   sig.complete ↔ ∀ (m : sig.M) (pk : sig.PK) (sk : sig.SK) (σ : sig.S)
--     (cache cache' : sig.random_spec.query_cache),
--     ((pk, sk), cache) ∈ (default_simulate sig.baseₛₒ $ sig.gen ()).support →
--     (σ, cache') ∈ (simulate sig.baseₛₒ (sig.sign (pk, sk, m)) cache).support →
--     (simulate' sig.baseₛₒ (sig.verify (pk, m, σ)) cache').support = {tt} :=
-- begin
--   simp_rw [complete, prob_output_eq_one_iff_subset],
--   refine ⟨λ h m pk sk σ cache cache' hgen hsign, _, λ h m, _⟩,
--   { rw [support_eq_singleton_iff_forall],
--     refine λ b hb, h m _,
--     simp only [support_completeness_experiment, set.mem_Union],
--     refine ⟨pk, sk, σ, cache, cache', hgen, hsign, hb⟩ },
--   { rw [support_completeness_experiment],
--     intros x hx,
--     simp only [set.mem_Union] at hx,
--     obtain ⟨pk, sk, σ, cache, cache', hgen, hsign, hb⟩ := hx,
--     specialize h m pk sk σ cache cache' hgen hsign,
--     exact h ▸ hb }
-- end

end complete

/-- An adversary for the unforgeable signature experiment.
  Note that the adversary only has access to the public key. -/
structure unforgeable_adversary (sig : signature) extends
  sec_adversary (uniform_selecting ++ sig.random_spec ++ sig.signing_spec) sig.PK (sig.M × sig.S)

namespace unforgeable_adversary

variables {sig : signature} (adversary : unforgeable_adversary sig)

/-- Wrapper function for simulation that hides the "state values" of the stateless oracles.
Runs the adversary with a signing oracle based on the provided public/secret keys,
returning the results of the adversary, and a log of the queries made by the adversary -/
def simulate_signing_oracle (pk : sig.PK) (sk : sig.SK) :
  oracle_comp (uniform_selecting ++ sig.random_spec)
    ((sig.M × sig.S) × (sig.M ↦ₒ sig.S).query_cache) :=
(prod.map id prod.snd) <$> (default_simulate (idₛₒ ++ₛ sig.signingₛₒ pk sk) (adversary.run pk))

-- instance has_sim_oracle (adv : sig.unforgeable_adversary) :
--   adv.has_sim_oracle sig.SK (uniform_selecting ++ sig.random_spec) (sig.M ↦ₒ sig.S).query_cache :=
-- { so := λ pk sk, sim_oracle.mask_state (idₛₒ ++ₛ sig.signingₛₒ pk sk) (equiv.punit_prod _)}

def unforgeable_experiment (sig : signature) : sec_experiment
  (uniform_selecting ++ sig.random_spec ++ sig.signing_spec)
  (uniform_selecting ++ sig.random_spec)
  sig.PK (sig.M × sig.S) sig.SK (sig.M ↦ₒ sig.S).query_cache :=
{ inp_gen := sig.gen (),
  so := λ ks, (sim_oracle.mask_state (idₛₒ ++ₛ sig.signingₛₒ ks.1 ks.2) (equiv.punit_prod _)),
  is_valid := λ ks ⟨⟨m, σ⟩, cache⟩, do {b ← sig.verify (ks.1, m, σ),
    return (b ∧ cache.lookup () m = none)} }

noncomputable def unforgeable_advantage (sig : signature) (adv : unforgeable_adversary sig) : ℝ≥0∞ :=
adv.advantage (unforgeable_experiment sig) (idₛₒ ++ₛ randomₛₒ)
  -- (idₛₒ ++ₛ sig.signingₛₒ ks.1 ks.2).mask_state _}

-- noncomputable def unforgeable_experiment :
--   sec_experiment

/-- Experiement for testing if a signature scheme is unforgeable.
Generate the public/secret keys, then simulate the adversary to get a signature.
Adversary succeeds if the signature verifies and the message hasn't been queried -/
noncomputable def experiment (sig : signature) (adversary : unforgeable_adversary sig) :
  oracle_comp uniform_selecting bool :=
default_simulate' (idₛₒ ++ₛ randomₛₒ)
(do {(pk, sk) ← sig.gen (),
  ((m, σ), cache) ← adversary.simulate_signing_oracle pk sk,
  b ← sig.verify (pk, m, σ),
  return (b ∧ cache.lookup () m = none)})

/-- Adversaries success at forging a signature. -/
noncomputable def advantage {sig : signature} (adversary : unforgeable_adversary sig) : ℝ≥0∞ :=
⁅(= tt) | adversary.experiment sig⁆

end unforgeable_adversary

end signature

/-- signature scheme is a set of signature algorithms indexed by a security parameter -/
def signature_scheme := Π (sp : ℕ), signature

namespace signature_scheme

open signature

/-- Scheme is complete if it is complete for each security parameter -/
def complete (sig_scheme : signature_scheme) : Prop :=
∀ (sp : ℕ), (sig_scheme sp).complete

/-- Signature scheme is unforgeable if any polynomial time adversary has negligible advantage in
  `unforgeable_experiment` as the security parameter grows -/
def unforgeable (sig_scheme : signature_scheme) : Prop :=
∀ (adversary : Π (sp : ℕ), unforgeable_adversary $ sig_scheme sp),
    negligable (λ sp, (adversary sp).advantage)

end signature_scheme