import computational_monads.probabalistic_computation.constructions
import computational_complexity.complexity_class
import data.list.basic

/-!
# Cryptographic Signature Schemes

This file defines signature algorithms and security properties for them.

Note that the schemes assume algorithms have access to a shared random oracle.
Signature schemes that don't need this can assume a random oracle like `⊥ → ()`, 
  which won't actually be query-able since `⊥` is an uninhabited type
-/

open prob_comp oracle_comp

/-- Signature on messages `M`, public and secret keys `PK` and `SK`, signatures of type `S`. 
  `oracle_access` specifies the oracles the algorithm can make use of  -/
structure signature (oracle_access : oracle_comp_spec)
  (M PK SK S : Type) [decidable_eq M] [decidable_eq PK] :=
(gen : unit → oracle_comp oracle_access (PK × SK))
(sign : PK × SK × M → oracle_comp oracle_access S)
(verify : PK × M × S → oracle_comp oracle_access bool)

namespace signature

variables {M PK SK S ROI ROO : Type}
  [decidable_eq M] [decidable_eq PK]
  [decidable_eq ROI] [fintype ROO]
  [inhabited ROO]
variable (sig : signature ⟦ROI →ᵒ ROO⟧ M PK SK S)

section complete

def completeness_experiment (m : M) : prob_comp bool :=
(do {
  (pk, sk) ← sig.gen (),
  σ ← sig.sign (pk, sk, m),
  b ← sig.verify (pk, m, σ),
  return b
}).simulate_result (random_oracle ROI ROO) []

-- @[simp]
-- lemma mem_completeness_experiment_iff (m : M) (b : bool) :
--   b ∈ (completeness_experiment sig m).alg.support ↔
--     ∃ (pk : PK) (sk : SK) (hks : (pk, sk) ∈ (sig.gen ()).support)
--       (σ : S) log (hσ : (σ, log) ∈ ((sig.sign (pk, sk, m)).simulate (random_simulation_oracle _ _) []).support)
--       (b' : bool) log' (hb' : (b', log') ∈ ((sig.verify (pk, m, σ)).simulate (random_simulation_oracle _ _) log).support),
--       b = b' :=
-- by simp [completeness_experiment]

def complete :=
∀ (m : M), (completeness_experiment sig m).prob_success = 1

end complete

end signature

variables [function_cost_model ℚ] [comp_cost_model ℚ]

structure signature_scheme (oracle_access : oracle_comp_spec)
  [oracle_comp_cost_model ℚ oracle_access]
  (M : Type) (PK SK S ROI ROO : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp] :=
(sig (sp : ℕ) : signature oracle_access M (PK sp) (SK sp) (S sp))
(gen_polnomial_complexity : complexity_class.polynomial_complexity (λ sp, (sig sp).gen))
(sign_polynomial_complexity : complexity_class.polynomial_complexity (λ sp, (sig sp).sign))
(verify_polynomial_complexity : complexity_class.polynomial_complexity (λ sp, (sig sp).verify))

namespace signature_scheme

variables (oracle_access : oracle_comp_spec)
  [oracle_comp_cost_model ℚ oracle_access]
  (M : Type) (PK SK S ROI ROO : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp]
  (sig_scheme : signature_scheme oracle_access M PK SK S ROI ROO)

section unforgeable

-- def unforgeable : Prop :=

end unforgeable

end signature_scheme