import data.list.basic

import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.constructions.logging.random_oracle
import computational_monads.simulation_semantics.constructions.identity_oracle
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable

/-!
# Cryptographic Signature Schemes

This file defines signature algorithms and security properties for them.

Note that the schemes assume algorithms have access to a shared random oracle.
Signature schemes that don't need this can assume a random oracle like `⊥ → ()`, 
  which won't actually be query-able since `⊥` is an uninhabited type
-/

open_locale ennreal nnreal
open oracle_comp oracle_spec distribution_semantics

/-- Signature on messages `M`, public and secret keys `PK` and `SK`, signatures of type `S`. 
  We model the algorithms as having access to a uniform selection oracle,
    and a set of random oracles that the algorithm has access to.
  If not in the random oracle model, can just take `random_oracles := []ₒ`, the empty `oracle_spec`
  We also bundle the polynomial complexity of the algorithms into the structure. -/
structure signature (M PK SK S : Type) :=
-- Random oracles for the algorithms, with finite ranges and computablity requirements.
(random_oracles : oracle_spec)
(random_oracles_finite_range : random_oracles.finite_range)
(random_oracles_computable : random_oracles.computable)
-- The actual algorithms of the signature scheme.
(gen : unit → oracle_comp (uniform_selecting ++ random_oracles) (PK × SK))
(sign : PK × SK × M → oracle_comp (uniform_selecting ++ random_oracles) S)
(verify : PK × M × S → oracle_comp (uniform_selecting ++ random_oracles) bool)
-- Requirement that all the algorithms have polynomial time complexity.
(gen_poly_time : poly_time_oracle_comp gen)
(sign_poly_time : poly_time_oracle_comp sign)
(verify_poly_time : poly_time_oracle_comp verify)

namespace signature

variables {A M PK SK S : Type}
variables [inhabited S] [decidable_eq M] [decidable_eq S]

instance random_oracles.finite_range (sig : signature M PK SK S) :
  sig.random_oracles.finite_range :=
sig.random_oracles_finite_range

instance random_oracles.computable (sig : signature M PK SK S) :
  sig.random_oracles.computable :=
sig.random_oracles_computable

/-- Shorthand for the combination of the `uniform_selecting` oracle and the `random_oracles`-/
@[reducible, inline, derive finite_range, derive computable]
def oracles (sig : signature M PK SK S) :
  oracle_spec :=
uniform_selecting ++ sig.random_oracles

/-- A signing oracle corresponding to a given signature scheme -/
@[reducible, inline]
def signing_oracle_spec (sig : signature M PK SK S) : oracle_spec :=
(M →ₒ S)

/-- Simulate a computation with access to a `signing_oracle_spec` on top of standard oracles.
  The signature is derived by using the provided secret key `sk` -/
def signing_oracle (sig : signature M PK SK S) (pk : PK) (sk : SK) :
  simulation_oracle sig.signing_oracle_spec sig.oracles :=
⟪λ _ m, sig.sign (pk, sk, m)⟫ ∘ₛ (logging_oracle (M →ₒ S))

section complete

/-- Generate a key, sign on the given message, and return the result of verify on the signature.
  Random oracles have a shared cache for the entire computation,
  and the uniform selection oracle just forwards its query on. -/
noncomputable def completeness_experiment (sig : signature M PK SK S) (m : M) :
  oracle_comp uniform_selecting bool :=
default_simulate' (idₛ ⟪++⟫ random_oracle sig.random_oracles) 
(do { 
  (pk, sk) ← sig.gen (),
  σ ← sig.sign (pk, sk, m),
  sig.verify (pk, m, σ) 
})

@[simp]
lemma support_completeness_experiment (sig : signature M PK SK S) (m : M) :
  (completeness_experiment sig m).support =
    ⋃ (k : PK × SK) (hk : k ∈ (sig.gen ()).support)
      (σ : S) (hσ : σ ∈ (sig.sign (k.1, k.2, m)).support),
        (sig.verify (k.1, m, σ)).support :=
begin
  rw [completeness_experiment],
  simp [completeness_experiment],
  sorry
end

/-- Signature is complete if for any possible message, the generated signature is valid,
  i.e. the output of `sign` always returns true when `verify` is called.
  TODO: A more general version could allow for a negligable failure probability. -/
def complete (sig : signature M PK SK S) :=
∀ (m : M), ⦃ completeness_experiment sig m ⦄ tt = 1

lemma complete_iff_signatures_support_subset (sig : signature M PK SK S) :
  sig.complete ↔ ∀ (m : M) (pk : PK) (sk : SK) (σ : S),
    (pk, sk) ∈ (sig.gen ()).support → σ ∈ (sig.sign (pk, sk, m)).support
      → ff ∉ (sig.verify (pk, m, σ)).support :=
begin
  refine ⟨λ h m pk sk σ hgen hsign, _, λ h, _⟩,
  { specialize h m,
    rw distribution_semantics.eval_distribution_eq_one_iff_support_subset_singleton at h,
    simp [support_completeness_experiment, set.Union_subset_iff,
      prob_event_eq_one_iff_support_subset, prod.forall] at h,
    sorry,
    --exact λ h', (h pk sk hgen σ hsign h').elim
  },
  { intro m,
    simp [eval_distribution_eq_one_iff_support_subset_singleton,
      support_completeness_experiment],
    sorry,
    --exact λ pk sk hgen σ hsign, h m pk sk σ hgen hsign
  }
end

end complete

section unforgeable

variables [inhabited S] [decidable_eq M] [decidable_eq S]

-- TODO: could use `unforgeable` namespace with `unforgeable.adversary_oracles`?

/-- The adversary for the signing experiment has access to both the signature scheme's oracles,
  and a signing oracle that will be simulated with the hidden secret key. -/
@[reducible, inline, derive computable]
def unforgeable_adversary_oracle_spec (sig : signature M PK SK S) : oracle_spec :=
sig.oracles ++ (signing_oracle_spec sig)

/-- Oracle for unforgeable experiment uses the public and S-/
def unforgeable_adversary_oracle (sig : signature M PK SK S) (pk : PK) (sk : SK) :
  simulation_oracle sig.unforgeable_adversary_oracle_spec sig.oracles :=
idₛ ⟪++⟫ signing_oracle sig pk sk

/-- An adversary for the unforgeable signature experiment.
  Note that the adversary only has access to the public key. -/
structure unforgeable_adversary (sig : signature M PK SK S) :=
(adv : PK → oracle_comp (unforgeable_adversary_oracle_spec sig) (M × S))
(adv_poly_time : poly_time_oracle_comp adv)

/-- Wrapper function for simulation that hides the "state values" of the stateless oracles. -/
def simulate_adversary (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) (pk : PK) (sk : SK) :
  oracle_comp sig.oracles (M × S × query_log (M →ₒ S)) :=
do {
  ((m, s), (), log, ()) ←
    (default_simulate (unforgeable_adversary_oracle sig pk sk) (adversary.adv pk)),
  return (m, s, log)
}

/-- Experiement for testing if a signature scheme is unforgeable.
  Generate the public / secret keys, then simulate the adversary to get a signature.
  Adversary succeeds if the signature verifies and the message hasn't been queried -/
noncomputable def unforgeable_experiment (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) :
  oracle_comp uniform_selecting bool :=
default_simulate' (idₛ ⟪++⟫ random_oracle sig.random_oracles)
(do {
  (pk, sk) ← sig.gen (),
  (m, σ, log) ← simulate_adversary sig adversary pk sk,
  b ← sig.verify (pk, m, σ),
  return (b ∧ log.not_queried () m)
})

/-- Adversaries success at forging a signature.
  TODO: maybe this doesn't need an independent definition -/
noncomputable def unforgeable_advantage (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) : ℝ≥0∞ :=
⦃ (= tt) | unforgeable_experiment sig adversary ⦄

end unforgeable

end signature

/-- signature scheme is a set of signature algorithms indexed by a security parameter -/
def signature_scheme (M PK SK S : ℕ → Type) :=
Π (sp : ℕ), signature (M sp) (PK sp) (SK sp) (S sp)

namespace signature_scheme

open signature

variables {M PK SK S : ℕ → Type}
  [∀ sp, inhabited $ S sp] [∀ sp, decidable_eq $ M sp] [∀ sp, decidable_eq $ S sp]

/-- Scheme is complete if it is complete for each security parameter -/
def complete (sig_scheme : signature_scheme M PK SK S) : Prop :=
∀ (sp : ℕ), (sig_scheme sp).complete

/-- Signature scheme is unforgeable if any polynomial time adversary has negligible advantage in
  `unforgeable_experiment` as the security parameter grows -/
def unforgeable (sig_scheme : signature_scheme M PK SK S) : Prop :=
∀ (adversary : Π (sp : ℕ), unforgeable_adversary $ sig_scheme sp),
  negligable (λ sp, unforgeable_advantage (sig_scheme sp) (adversary sp))

end signature_scheme