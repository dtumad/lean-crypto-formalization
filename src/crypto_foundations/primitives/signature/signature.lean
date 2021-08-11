import crypto_foundations.computational_monads.dist_sem
import crypto_foundations.computational_monads.vector_call
import crypto_foundations.computational_monads.random_oracle
import computational_complexity.complexity_class
import computational_complexity.negligable
import data.list.basic

structure signature (M PK SK S ROI ROO : Type)
  [decidable_eq M] [decidable_eq PK]
  [decidable_eq ROI] [fintype ROO]
  [inhabited ROO] :=
(gen : unit → comp (PK × SK))
(gen_is_well_formed : ∀ x, (gen x).is_well_formed)
(sign : SK × M → random_oracle_comp ROI ROO S)
(sign_is_well_formed : ∀ x, (sign x).is_well_formed)
(verify : PK × S → random_oracle_comp ROI ROO bool)
(verify_is_well_formed : ∀ x, (verify x).is_well_formed)

namespace signature

variables {M PK SK S ROI ROO : Type}
  [decidable_eq M] [decidable_eq PK]
  [decidable_eq ROI] [fintype ROO]
  [inhabited ROO]
variable (sig : signature M PK SK S ROI ROO)

section is_well_formed_instances

@[simp]
instance gen.is_well_formed (u : unit) :
  (sig.gen u).is_well_formed :=
sig.gen_is_well_formed _

@[simp]
instance sign.is_well_formed (inp : SK × M) :
  (sig.sign inp).is_well_formed :=
sig.sign_is_well_formed _

@[simp]
instance verify.is_well_formed (inp : PK × S) :
  (sig.verify inp).is_well_formed :=
sig.verify_is_well_formed _

end is_well_formed_instances

section complete

def completeness_experiment (m : M) : comp bool :=
do (pk, sk) ← sig.gen (),
  (σ, log) ← (sig.sign (sk, m)).simulate [],
  (b, _) ← (sig.verify (pk, σ)).simulate log,
  return b

@[simp]
-- TODO: I think it should be possible to write a derive handler for this
instance comleteness_experiment.is_well_formed (m : M) : 
  (completeness_experiment sig m).is_well_formed :=
by simp [completeness_experiment]

@[simp]
lemma mem_completeness_experiment_iff (m : M) (b : bool) :
  b ∈ (completeness_experiment sig m).support ↔
    ∃ (pk : PK) (sk : SK) (hks : (pk, sk) ∈ (sig.gen ()).support)
      (σ : S) log (hσ : (σ, log) ∈ ((sig.sign (sk, m)).simulate []).support)
      (b' : bool) log' (hb' : (b', log') ∈ ((sig.verify (pk, σ)).simulate log).support),
      b = b' :=
by simp [completeness_experiment]

def complete :=
∀ (m : M), (completeness_experiment sig m).Pr = 1

end complete

end signature

variables [function_cost_model ℚ] [comp_cost_model ℚ]

structure signature_scheme (M : Type) (PK SK S ROI ROO : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp]
  [∀ sp, decidable_eq $ ROI sp] [∀ sp, fintype $ ROO sp]
  [∀ sp, inhabited $ ROO sp] :=
(sig (sp : ℕ) : signature M (PK sp) (SK sp) (S sp) (ROI sp) (ROO sp))
(gen_polnomial_complexity : complexity_class.polynomial_complexity (λ sp, (sig sp).gen))
(sign_polynomial_complexity : sorry) --complexity_class.polynomial_complexity (λ sp, (sig sp).sign))
(verify_polynomial_complexity : sorry)

namespace signature_scheme

variables (M : Type) (PK SK S ROI ROO : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp]
  [∀ sp, decidable_eq $ ROI sp] [∀ sp, fintype $ ROO sp]
  [∀ sp, inhabited $ ROO sp]
  (sigs : signature_scheme M PK SK S ROI ROO)

section unforgeable

def unforgeable : Prop := sorry

end unforgeable

end signature_scheme