import computational_monads.asymptotics.polynomial_time
import computational_monads.constructions.forking_lemma
import data.list.basic

/-!
# Cryptographic Signature Schemes

This file defines signature algorithms and security properties for them.

Note that the schemes assume algorithms have access to a shared random oracle.
Signature schemes that don't need this can assume a random oracle like `⊥ → ()`, 
  which won't actually be query-able since `⊥` is an uninhabited type
-/

open_locale ennreal nnreal

open oracle_comp oracle_spec

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

instance signature.random_oracles.finite_range (sig : signature M PK SK S) :
  sig.random_oracles.finite_range :=
sig.random_oracles_finite_range

instance signature.random_oracles.computable (sig : signature M PK SK S) :
  sig.random_oracles.computable :=
sig.random_oracles_computable

/-- Shorthand for the combination of the `uniform_selecting` oracle and the `random_oracles`-/
@[reducible, inline, derive finite_range, derive computable]
def oracles (sig : signature M PK SK S) :
  oracle_spec :=
uniform_selecting ++ sig.random_oracles

/-- Simulate a computation with access to the signatures random oracles,
  using a uniform selection oracle with cacheing of the previous queries-/
noncomputable def simulate_random_oracles
  {sig : signature M PK SK S} (oa : oracle_comp sig.oracles A) :
  oracle_comp uniform_selecting A :=
simulate' (identity_oracle uniform_selecting ⟪++⟫ random_simulation_oracle' sig.random_oracles)
  oa ((), query_log.init sig.random_oracles, ())

section complete

/-- Generate a key, sign on the given message, and return the result of verify on the signature.
  Random oracles have a shared cached state of previous queries, handled by a call to `simulate'` -/
noncomputable def completeness_experiment (sig : signature M PK SK S) (m : M) :
  oracle_comp uniform_selecting bool :=
simulate_random_oracles (do { 
  (pk, sk) ← sig.gen (),
  σ ← sig.sign (pk, sk, m),
  sig.verify (pk, m, σ) 
})

@[simp]
lemma support_completeness_experiment (sig : signature M PK SK S) (m : M) :
  (completeness_experiment sig m).support =
    ⋃ (k : PK × SK) (hk : k ∈ (sig.gen ()).support) (σ : S)
      (hσ : σ ∈ (sig.sign (k.1, k.2, m)).support),
        (sig.verify (k.1, m, σ)).support :=
begin
  simp [completeness_experiment],
end

/-- Honest signer always generates a valid message -/
def complete (sig : signature M PK SK S) :=
∀ (m : M), ⟦ completeness_experiment sig m ⟧ tt = 1

lemma complete_iff_signatures_support_subset (sig : signature M PK SK S) :
  sig.complete ↔ ∀ (m : M) (pk : PK) (sk : SK) (σ : S),
    (pk, sk) ∈ (sig.gen ()).support → σ ∈ (sig.sign (pk, sk, m)).support
      → ff ∉ (sig.verify (pk, m, σ)).support :=
begin
  refine ⟨λ h m pk sk σ hgen hsign, _, λ h, _⟩,
  { specialize h m,
    rw eval_distribution_eq_one_iff_support_subset_singleton at h,
    simp [support_completeness_experiment, set.Union_subset_iff,
      eval_prob_eq_one_iff_support_subset, prod.forall] at h,
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

/-- An adversary for the unforgeable signature experiment.
  Note that the adversary only has access to the public key. -/
structure unforgeable_adversary (sig : signature M PK SK S) :=
(adv : PK → oracle_comp (sig.oracles ++ (M →ₒ S)) (M × S))
(adv_poly_time : poly_time_oracle_comp adv)

/-- When we simulate the adversary, we forward the "coin flip" queries through.
  When simulating the signing, and then answer the query by using the secret key. -/
def simulate_sign (sig : signature M PK SK S) (pk : PK) (sk : SK) :
  simulation_oracle (sig.oracles ++ (M →ₒ S)) (sig.oracles) :=
identity_oracle sig.oracles ⟪++⟫
  (⟪λ _ m, sig.sign (pk, sk, m)⟫ ∘ₛ (logging_simulation_oracle (M →ₒ S)))

/-- Wrapper function for simulation that hides the "state values" of the stateless oracles. -/
def simulate_adversary (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) (pk : PK) (sk : SK) :
  oracle_comp sig.oracles (M × S × query_log (M →ₒ S)) :=
do {
  ((m, s), (), log, ()) ← (simulate (simulate_sign sig pk sk) (adversary.adv pk) ((), query_log.init _, ())),
  return (m, s, log)
}

/-- Experiement for testing if a signature scheme is unforgeable.
  Generate the public / secret keys, then simulate the adversary to get a signature.
  Adversary succeeds if the signature verifies and the message hasn't been queried -/
noncomputable def unforgeable_experiment (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) :
  oracle_comp uniform_selecting bool :=
simulate_random_oracles (do {
  (pk, sk) ← sig.gen (),
  (m, σ, log) ← simulate_adversary sig adversary pk sk,
  b ← sig.verify (pk, m, σ),
  return (b ∧ log.not_queried () m)
})

/-- Adversaries success at forging a signature.
  TODO: maybe this doesn't need an independent definition -/
noncomputable def unforgeable_advantage (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) : ℝ≥0∞ :=
⟦ (= tt) | unforgeable_experiment sig adversary ⟧

end unforgeable

end signature

/-- signature algorithms indexed by a security parameter -/
def signature_scheme (M PK SK S : ℕ → Type) :=
Π (sp : ℕ), signature (M sp) (PK sp) (SK sp) (S sp)

namespace signature_scheme

open signature

variables {M PK SK S : ℕ → Type}
  [∀ sp, inhabited $ S sp] [∀ sp, decidable_eq $ M sp] [∀ sp, decidable_eq $ S sp]

/-- Polynomial time adversary has negligible advantage in
  `unforgeable_experiment` as security parameter grows -/
def unforgeable (sig_scheme : signature_scheme M PK SK S) : Prop :=
∀ (adversary : Π (sp : ℕ), unforgeable_adversary $ sig_scheme sp),
  negligable (λ sp, unforgeable_advantage (sig_scheme sp) (adversary sp))

end signature_scheme