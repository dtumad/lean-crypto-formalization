/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.constructions.logging.random_oracle
import computational_monads.simulation_semantics.constructions.identity_oracle
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable

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
open oracle_comp oracle_spec distribution_semantics

/-- Signature on messages `M`, public and secret keys `PK` and `SK`, signatures of type `S`. 
  We model the algorithms as having access to a uniform selection oracle,
    and a set of random oracles that the algorithm has access to.
  If not in the random oracle model, can just take `random_oracles := []ₒ`, the empty `oracle_spec`
  We also bundle the polynomial complexity of the algorithms into the structure. -/
structure signature :=
-- Types of the possible messages, public keys, secret keys, and signatures
(M PK SK S : Type)
-- Equality between messages and between signatures is decidable (unneeded for `PK` and `SK`)
(decidable_eq_M : decidable_eq M)
(decidable_eq_S : decidable_eq S)
-- There exists at least one signature (in particular we can define a signing oracle)
(inhabited_S : inhabited S)
-- Random oracles for the algorithms, with finite ranges and computablity requirements.
(random_oracle_spec : oracle_spec)
(random_oracle_spec_finite_range : random_oracle_spec.finite_range)
(random_oracle_spec_computable : random_oracle_spec.computable)
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

section instances

instance random_oracle_spec.finite_range : sig.random_oracle_spec.finite_range :=
sig.random_oracle_spec_finite_range

instance random_oracle_spec.computable : sig.random_oracle_spec.computable :=
sig.random_oracle_spec_computable

instance decidable_eq_S' : decidable_eq sig.S := sig.decidable_eq_S

instance decidable_eq_M' : decidable_eq sig.M := sig.decidable_eq_M

instance inhabited_S' : inhabited sig.S := sig.inhabited_S

end instances

/-- Shorthand for the combination of the `uniform_selecting` oracle and the `random_oracles`,
  i.e. the oracles available to the signature algorithms themselves -/
@[reducible, inline, derive finite_range, derive computable]
def base_oracle_spec (sig : signature) : oracle_spec :=
uniform_selecting ++ sig.random_oracle_spec

/-- Simulate the basic oracles for the signature, using a random oracle in the natural way -/
noncomputable def base_oracle (sig : signature) :
  sim_oracle sig.base_oracle_spec uniform_selecting (query_log sig.random_oracle_spec) :=
sim_oracle.mask_state (idₛ ++ₛ random_oracle sig.random_oracle_spec)
  (equiv.punit_prod (query_log sig.random_oracle_spec))

/-- A signing oracle corresponding to a given signature scheme -/
@[reducible, inline, derive computable]
def signing_oracle_spec (sig : signature) [inhabited sig.S] : oracle_spec :=
(sig.M ↦ₒ sig.S)

/-- Simulate a computation with access to a `signing_oracle_spec` to one with `base_oracle_spec`,
  using the provided public/secret keys to answer queries for signatures.
Additionally it logs and returns a list queries to the signing oracle -/
def signing_oracle (sig : signature) (pk : sig.PK) (sk : sig.SK) :
  sim_oracle sig.signing_oracle_spec sig.base_oracle_spec (query_log (sig.M ↦ₒ sig.S)) :=
sim_oracle.mask_state (⟪λ _ m, sig.sign (pk, sk, m)⟫ ∘ₛ (logging_oracle (sig.M ↦ₒ sig.S)))
  (equiv.prod_punit (query_log (signing_oracle_spec sig)))

section complete

/-- Generate a key, sign on the given message, and return the result of verify on the signature.
  Random oracles have a shared cache for the entire computation,
  and the uniform selection oracle just forwards its query on. -/
noncomputable def completeness_experiment (sig : signature) (m : sig.M) :
  oracle_comp uniform_selecting bool :=
default_simulate' sig.base_oracle 
  (do {(pk, sk) ← sig.gen (), σ ← sig.sign (pk, sk, m), sig.verify (pk, m, σ)})

@[simp]
lemma support_completeness_experiment (m : sig.M) :
  (completeness_experiment sig m).support = ⋃ (pk : sig.PK) (sk : sig.SK) (σ : sig.S)
    (log log' : query_log sig.random_oracle_spec)
    (hk : ((pk, sk), log) ∈ (default_simulate sig.base_oracle $ sig.gen ()).support)
    (hσ : (σ, log') ∈ (simulate sig.base_oracle (sig.sign (pk, sk, m)) log).support),
      (simulate' sig.base_oracle (sig.verify (pk, m, σ)) log').support :=
begin
  sorry
end

/-- Signature is complete if for any possible message, the generated signature is valid,
  i.e. the output of `sign` always returns true when `verify` is called.
  note that this definition doesn't allow for negligable failure of signing -/
def complete (sig : signature) := ∀ (m : sig.M), ⦃completeness_experiment sig m⦄ tt = 1

-- TODO: fix like above
lemma complete_iff_signatures_support_subset :
  sig.complete ↔ ∀ (m : sig.M) (pk : sig.PK) (sk : sig.SK) (σ : sig.S)
    (log log' : query_log sig.random_oracle_spec),
    ((pk, sk), log) ∈ (default_simulate sig.base_oracle $ sig.gen ()).support →
    (σ, log') ∈ (simulate sig.base_oracle (sig.sign (pk, sk, m)) log).support →
    (simulate' sig.base_oracle (sig.verify (pk, m, σ)) log').support = {tt} :=
begin
  simp_rw [complete, eval_dist_eq_one_iff_support_eq_singleton,
    support_completeness_experiment], sorry,
end

end complete

section unforgeable

/-- The adversary for the signing experiment has access to both the signature scheme's oracles,
  and a signing oracle that will be simulated with the hidden secret key. -/
@[reducible, inline, derive computable]
def unforgeable_adversary_oracle_spec (sig : signature) : oracle_spec :=
uniform_selecting ++ sig.random_oracle_spec ++ sig.signing_oracle_spec

/-- An adversary for the unforgeable signature experiment.
  Note that the adversary only has access to the public key. -/
structure unforgeable_adversary (sig : signature) :=
(adv : sig.PK → oracle_comp (sig.unforgeable_adversary_oracle_spec) (sig.M × sig.S))
(adv_poly_time : poly_time_oracle_comp adv)

namespace unforgeable_adversary

variables {sig} (adversary : unforgeable_adversary sig)

/-- Wrapper function for simulation that hides the "state values" of the stateless oracles.
Runs the adversary with a signing oracle based on the provided public/secret keys,
  returning the results of the adversary, and a log of the queries made by the adversary
 -/
def simulate (pk : sig.PK) (sk : sig.SK) :
  oracle_comp sig.base_oracle_spec (sig.M × sig.S × query_log (sig.M ↦ₒ sig.S)) := 
do {
  ((m, s), _, log) ← (default_simulate (idₛ ++ₛ signing_oracle sig pk sk) (adversary.adv pk)),
  return (m, s, log)
}

end unforgeable_adversary

/-- Experiement for testing if a signature scheme is unforgeable.
  Generate the public/secret keys, then simulate the adversary to get a signature.
  Adversary succeeds if the signature verifies and the message hasn't been queried -/
noncomputable def unforgeable_experiment (sig : signature) (adversary : unforgeable_adversary sig) :
  oracle_comp uniform_selecting bool :=
default_simulate' (idₛ ++ₛ random_oracle sig.random_oracle_spec) (do {
  (pk, sk) ← sig.gen (),
  (m, σ, log) ← adversary.simulate pk sk,
  b ← sig.verify (pk, m, σ),
  return (if log.not_queried () m then b else ff)
})

namespace unforgeable_experiment

end unforgeable_experiment

/-- Adversaries success at forging a signature.
  TODO: maybe this doesn't need an independent definition -/
noncomputable def unforgeable_advantage (sig : signature)
  (adversary : unforgeable_adversary sig) : ℝ≥0∞ :=
⦃ (= tt) | unforgeable_experiment sig adversary ⦄

namespace unforgeable_advantage

end unforgeable_advantage

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
  negligable (λ sp, unforgeable_advantage (sig_scheme sp) (adversary sp))

end signature_scheme