import computational_monads.probabalistic_computation.constructions
import computational_complexity.complexity_class
import computational_complexity.negligable
import data.list.basic

/-!
# Cryptographic Signature Schemes

This file defines signature algorithms and security properties for them.

Note that the schemes assume sign and verify have access to a shared random oracle.
Signature schemes that don't need this can assume a random oracle like `⊥ → ()`, 
  which won't actually be query-able since `⊥` is an uninhabited type
-/

open prob_comp oracle_comp

/-- Signature on messages `M`, public and secret keys `PK` and `SK`,
  signatures of type `S`, given access to a random oracle `ROD → ROR` -/
structure signature (M PK SK S ROD ROR : Type)
  [decidable_eq M] [decidable_eq PK]
  [decidable_eq ROD] [fintype ROR]
  [inhabited ROR] :=
(gen : unit → prob_comp (PK × SK))
(sign : PK × SK × M → oracle_comp (oracle_comp_spec.random_oracle_spec ROD ROR) S)
(verify : PK × M × S → oracle_comp (oracle_comp_spec.random_oracle_spec ROD ROR) bool)

namespace signature

variables {M PK SK S ROI ROO : Type}
  [decidable_eq M] [decidable_eq PK]
  [decidable_eq ROI] [fintype ROO]
  [inhabited ROO]
variable (sig : signature M PK SK S ROI ROO)

section complete

def completeness_experiment (m : M) : prob_comp bool :=
do (pk, sk) ← sig.gen (),
  (σ, log) ← (sig.sign (pk, sk, m)).simulate (random_oracle ROI ROO) [],
  (b, _) ← (sig.verify (pk, m, σ)).simulate (random_oracle ROI ROO) log,
  return b

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
  [Π (spec : oracle_comp_spec), oracle_comp_cost_model ℚ spec]

structure signature_scheme (M : Type) (PK SK S ROI ROO : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp]
  [∀ sp, decidable_eq $ ROI sp] [∀ sp, fintype $ ROO sp]
  [∀ sp, inhabited $ ROO sp] :=
(sig (sp : ℕ) : signature M (PK sp) (SK sp) (S sp) (ROI sp) (ROO sp))
(gen_polnomial_complexity : complexity_class.polynomial_complexity (λ sp, (sig sp).gen))
(sign_polynomial_complexity : complexity_class.polynomial_complexity (λ sp, (sig sp).sign))
(verify_polynomial_complexity : complexity_class.polynomial_complexity (λ sp, (sig sp).verify))

namespace signature_scheme

variables (M : Type) (PK SK S ROI ROO : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp]
  [∀ sp, decidable_eq $ ROI sp] [∀ sp, fintype $ ROO sp]
  [∀ sp, inhabited $ ROO sp]
  (sig_scheme : signature_scheme M PK SK S ROI ROO)

section unforgeable

-- def unforgeable : Prop := sorry

end unforgeable

end signature_scheme