/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.random_oracle
import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.identity_oracle
import computational_monads.simulation_semantics.oracle_append
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable
import computational_monads.asymptotics.queries_at_most
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

open_locale ennreal nnreal
open oracle_comp oracle_spec

/-- Signature on messages `M`, public and secret keys `PK` and `SK`, signatures of type `S`.
  We model the algorithms as having access to a uniform selection oracle,
    and a set of random oracles that the algorithm has access to.
  If not in the random oracle model, can just take `random_oracles := []ₒ`, the empty `oracle_spec`
  We also bundle the polynomial complexity of the algorithms into the structure. -/
structure signature := -- TODO: signature_alg?
-- Types of the possible messages, public keys, secret keys, and signatures
(M PK SK S : Type)
-- Equality between messages and between signatures is decidable (unneeded for `PK` and `SK`)
(decidable_eq_M : decidable_eq M)
(decidable_eq_S : decidable_eq S)
-- There exists at least one signature (in particular we can define a signing oracle)
(inhabited_S : inhabited S)
-- There are a finite number of possible signatures
(fintype_S : fintype S)
-- Set of random oracles available to the signature algorithms
(random_oracle_spec : oracle_spec)
-- The actual algorithms of the signature scheme.
(gen : unit → oracle_comp (uniform_selecting ++ random_oracle_spec) (PK × SK))
(sign : PK × SK × M → oracle_comp (uniform_selecting ++ random_oracle_spec) S)
(verify : PK × M × S → oracle_comp (uniform_selecting ++ random_oracle_spec) bool)
-- Requirement that all the algorithms have polynomial time complexity.
-- (gen_poly_time : poly_time_oracle_comp gen)
-- (sign_poly_time : poly_time_oracle_comp sign)
-- (verify_poly_time : poly_time_oracle_comp verify)

namespace signature

variable (sig : signature)

section oracle_instances

instance decidable_eq_S' : decidable_eq sig.S := sig.decidable_eq_S

instance decidable_eq_M' : decidable_eq sig.M := sig.decidable_eq_M

instance inhabited_S' : inhabited sig.S := sig.inhabited_S

instance fintype_S' : fintype sig.S := sig.fintype_S

end oracle_instances

section oracle_spec

/-- Shorthand for the combination of the `uniform_selecting` oracle and the `random_oracles`,
  i.e. the oracles available to the signature algorithms themselves -/
@[reducible, inline] def base_oracle_spec (sig : signature) :
  oracle_spec := uniform_selecting ++ sig.random_oracle_spec

/-- Simulate the basic oracles for the signature, using `random_oracle` to simulate the
random oracle and preserving the `uniform_selecting` oracle as is. -/
noncomputable def base_oracle (sig : signature) :
  sim_oracle sig.base_oracle_spec uniform_selecting (query_cache sig.random_oracle_spec) :=
sim_oracle.mask_state (idₛ ++ₛ randomₛₒ)
  (equiv.punit_prod (query_cache sig.random_oracle_spec))

/-- A signing oracle corresponding to a given signature scheme -/
@[reducible, inline]
def signing_oracle_spec (sig : signature) [inhabited sig.S] : oracle_spec := sig.M ↦ₒ sig.S

/-- Simulate a computation with access to a `signing_oracle_spec` to one with `base_oracle_spec`,
  using the provided public/secret keys to answer queries for signatures.
Additionally it logs and returns a list queries to the signing oracle -/
def signing_oracle (sig : signature) (pk : sig.PK) (sk : sig.SK) :
  sim_oracle sig.signing_oracle_spec sig.base_oracle_spec (query_cache (sig.M ↦ₒ sig.S)) :=
sim_oracle.mask_state (⟪λ _ m, sig.sign (pk, sk, m)⟫ ∘ₛ cachingₛₒ)
  (equiv.prod_punit (query_cache (signing_oracle_spec sig)))

end oracle_spec

section complete

/-- Generate a key, sign on the given message, and return the result of verify on the signature.
  Random oracles have a shared cache for the entire computation,
  and the uniform selection oracle just forwards its query on. -/
noncomputable def completeness_experiment (sig : signature) (m : sig.M) :
  oracle_comp uniform_selecting bool :=
default_simulate' sig.base_oracle
(do { (pk, sk) ← sig.gen (),
      σ ← sig.sign (pk, sk, m),
      sig.verify (pk, m, σ) })

lemma completeness_experiment.def (m : sig.M) : sig.completeness_experiment m = default_simulate'
  sig.base_oracle (do {k ← sig.gen (), σ ← sig.sign (k.1, k.2, m), sig.verify (k.1, m, σ)}) :=
begin
  rw [completeness_experiment],
  congr,
  refine funext (λ x, _),
  cases x,
  simp [completeness_experiment._match_1],
end

/-- The possible outputs of running the completeness experiment,
  as a union over the keys and signature generated, plus internal random oracle caches. -/
@[simp] lemma support_completeness_experiment (m : sig.M) :
  (completeness_experiment sig m).support = ⋃ (pk : sig.PK) (sk : sig.SK) (σ : sig.S)
    (cache cache' : query_cache sig.random_oracle_spec)
    (hk : ((pk, sk), cache) ∈ (default_simulate sig.base_oracle $ sig.gen ()).support)
    (hσ : (σ, cache') ∈ (simulate sig.base_oracle (sig.sign (pk, sk, m)) cache).support),
      (simulate' sig.base_oracle (sig.verify (pk, m, σ)) cache').support :=
begin
  ext x,
  simp only [completeness_experiment.def, default_simulate',
    support_simulate'_bind, set.mem_Union],
  sorry,
end

/-- Signature is complete if for any possible message, the generated signature is valid,
  i.e. the output of `sign` always returns true when `verify` is called.
  note that this definition doesn't allow for negligable failure of signing -/
def complete (sig : signature) := ∀ (m : sig.M), ⁅= tt | completeness_experiment sig m⁆ = 1

lemma complete_iff_signatures_support_subset :
  sig.complete ↔ ∀ (m : sig.M) (pk : sig.PK) (sk : sig.SK) (σ : sig.S)
    (cache cache' : query_cache sig.random_oracle_spec),
    ((pk, sk), cache) ∈ (default_simulate sig.base_oracle $ sig.gen ()).support →
    (σ, cache') ∈ (simulate sig.base_oracle (sig.sign (pk, sk, m)) cache).support →
    (simulate' sig.base_oracle (sig.verify (pk, m, σ)) cache').support = {tt} :=
begin
  simp_rw [complete, prob_output_eq_one_iff_subset],
  refine ⟨λ h m pk sk σ cache cache' hgen hsign, _, λ h m, _⟩,
  { rw [support_eq_singleton_iff_forall],
    refine λ b hb, h m _,
    simp only [support_completeness_experiment, set.mem_Union],
    refine ⟨pk, sk, σ, cache, cache', hgen, hsign, hb⟩ },
  { rw [support_completeness_experiment],
    intros x hx,
    simp only [set.mem_Union] at hx,
    obtain ⟨pk, sk, σ, cache, cache', hgen, hsign, hb⟩ := hx,
    specialize h m pk sk σ cache cache' hgen hsign,
    exact h ▸ hb }
end

end complete

section unforgeable

/-- The adversary for the signing experiment has access to both the signature scheme's oracles,
  and a signing oracle that will be simulated with the hidden secret key. -/
@[reducible, inline]
def unforgeable_adversary_oracle_spec (sig : signature) : oracle_spec :=
sig.random_oracle_spec ++ sig.signing_oracle_spec

/-- An adversary for the unforgeable signature experiment.
  Note that the adversary only has access to the public key. -/
def unforgeable_adversary (sig : signature) :=
sec_adversary (sig.unforgeable_adversary_oracle_spec) sig.PK (sig.M × sig.S)


-- structure unforgeable_adversary (sig : signature) :=
-- (adv : sig.PK → oracle_comp (sig.unforgeable_adversary_oracle_spec) (sig.M × sig.S))
-- (adv_poly_time : poly_time_oracle_comp adv)
-- (query_bound : ℕ)
-- (adv_queries_at_most : ∀ pk, queries_at_most (adv pk) query_bound)

namespace unforgeable_adversary

variables {sig} (adversary : unforgeable_adversary sig)

/-- Wrapper function for simulation that hides the "state values" of the stateless oracles.
Runs the adversary with a signing oracle based on the provided public/secret keys,
  returning the results of the adversary, and a log of the queries made by the adversary
 -/
def simulate (pk : sig.PK) (sk : sig.SK) :
  oracle_comp sig.base_oracle_spec (sig.M × sig.S × query_cache (sig.M ↦ₒ sig.S)) :=
do{ ((m, s), _, log) ← (default_simulate (idₛ ++ₛ signing_oracle sig pk sk) (adversary.run pk)),
    return (m, s, log) }

/-- Experiement for testing if a signature scheme is unforgeable.
  Generate the public/secret keys, then simulate the adversary to get a signature.
  Adversary succeeds if the signature verifies and the message hasn't been queried -/
noncomputable def experiment (sig : signature) (adversary : unforgeable_adversary sig) :
  oracle_comp uniform_selecting bool :=
default_simulate' (idₛ ++ₛ randomₛₒ)
(do { (pk, sk) ← sig.gen (),
      (m, σ, cache) ← adversary.simulate pk sk,
      b ← sig.verify (pk, m, σ),
      m' : (sig.M ↦ₒ sig.S).domain () ← return m,
      return (if m' ∉ᵢ cache then b else ff) })

/-- Adversaries success at forging a signature. -/
noncomputable def advantage {sig : signature} (adversary : unforgeable_adversary sig) : ℝ≥0∞ :=
⁅(= tt) | adversary.experiment sig⁆

end unforgeable_adversary

end unforgeable

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
  -- (∃ (p : polynomial ℕ), ∀ n, (adversary n).query_bound ≤ p.eval n) →
  negligable (λ sp, (adversary sp).advantage)

end signature_scheme