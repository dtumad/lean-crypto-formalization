import computational_monads.dist_sem
import computational_monads.vector_call
import computational_monads.random_oracle
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

/-- Signature on messages `M`, public and secret keys `PK` and `SK`,
  signatures of type `S`, given access to a random oracle `ROD → ROR` -/
structure signature (M PK SK S ROD ROR : Type)
  [decidable_eq M] [decidable_eq PK]
  [decidable_eq ROD] [fintype ROR]
  [inhabited ROR] :=
(gen : unit → comp (PK × SK))
(sign : PK × SK × M → oracle_comp (oracle_comp_spec.random_oracle_spec ROD ROR) S)
(verify : PK × M × S → oracle_comp (oracle_comp_spec.random_oracle_spec ROD ROR) bool)

namespace signature

variables {M PK SK S ROI ROO : Type}
  [decidable_eq M] [decidable_eq PK]
  [decidable_eq ROI] [fintype ROO]
  [inhabited ROO]
variable (sig : signature M PK SK S ROI ROO)

section is_well_formed_instances

class is_well_formed (sig : signature M PK SK S ROI ROO) :=
(gen_is_well_formed : ∀ inp, (sig.gen inp).is_well_formed)
(sign_is_well_formed : ∀ inp, (sig.sign inp).is_well_formed)
(verify_is_well_formed : ∀ inp, (sig.verify inp).is_well_formed)

@[simp]
instance gen.is_well_formed [sig.is_well_formed] (u : unit) :
  (sig.gen u).is_well_formed :=
signature.is_well_formed.gen_is_well_formed _

@[simp]
instance sign.is_well_formed [sig.is_well_formed] (inp : PK × SK × M) :
  (sig.sign inp).is_well_formed :=
signature.is_well_formed.sign_is_well_formed _

@[simp]
instance verify.is_well_formed [sig.is_well_formed] (inp : PK × M × S) :
  (sig.verify inp).is_well_formed :=
signature.is_well_formed.verify_is_well_formed _

end is_well_formed_instances

variable [sig.is_well_formed]

section complete

def completeness_experiment (m : M) : comp bool :=
do (pk, sk) ← sig.gen (),
  (σ, log) ← (sig.sign (pk, sk, m)).simulate (random_simulation_oracle _ _) [],
  (b, _) ← (sig.verify (pk, m, σ)).simulate (random_simulation_oracle _ _) log,
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
      (σ : S) log (hσ : (σ, log) ∈ ((sig.sign (pk, sk, m)).simulate (random_simulation_oracle _ _) []).support)
      (b' : bool) log' (hb' : (b', log') ∈ ((sig.verify (pk, m, σ)).simulate (random_simulation_oracle _ _) log).support),
      b = b' :=
by simp [completeness_experiment]

def complete :=
∀ (m : M), (completeness_experiment sig m).Pr = 1

end complete

end signature

variables [function_cost_model ℚ] [comp_cost_model ℚ]
  [Π (spec : oracle_comp_spec), oracle_comp_cost_model ℚ spec]

structure signature_scheme (M : Type) (PK SK S ROI ROO : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp]
  [∀ sp, decidable_eq $ ROI sp] [∀ sp, fintype $ ROO sp]
  [∀ sp, inhabited $ ROO sp] :=
(sig (sp : ℕ) : signature M (PK sp) (SK sp) (S sp) (ROI sp) (ROO sp))
(sig_is_well_formed : ∀ sp, (sig sp).is_well_formed)
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