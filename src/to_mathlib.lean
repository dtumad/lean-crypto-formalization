import data.bitvec.basic
import measure_theory.probability_mass_function
import algebra.big_operators

open_locale big_operators nnreal

/-- Collection of random statements that should eventually port to mathlib -/

variables {A B : Type*}

@[simp] lemma card_bitvec {n : ℕ} : fintype.card (bitvec n) = 2 ^ n :=
by rw [card_vector n, fintype.card_bool]

lemma sum_inv_fintype_card_eq_one {A : Type*} [fintype A] [inhabited A] :
  has_sum (λ (a : A), (fintype.card A : nnreal)⁻¹) 1 :=
begin
  convert has_sum_fintype (λ (a : A), (fintype.card A : nnreal)⁻¹),
  rw [finset.sum_const, nsmul_eq_mul],
  refine (div_self _).symm,
  rw [ne.def, nat.cast_eq_zero],
  exact finset.card_ne_zero_of_mem (by simp : arbitrary A ∈ _),
end

noncomputable def pmf.const (α : Type*) [fintype α] [inhabited α] : pmf α :=
⟨λ a, (fintype.card α : nnreal)⁻¹, sum_inv_fintype_card_eq_one⟩

@[simp] lemma pmf.const_apply {α : Type*} [fintype α] [inhabited α]
  (a : α) : pmf.const α a = (fintype.card α : nnreal)⁻¹ := rfl

def decidable_eq_of_prod_left {A B : Type*} [inhabited B] [h : decidable_eq (A × B)] : 
  decidable_eq A :=
λ a a', decidable.rec (λ h, is_false (λ h', h (prod.mk.inj_iff.mpr ⟨h', rfl⟩))) 
  (λ h, is_true (prod.mk.inj_iff.mp h).1) (h ⟨a, arbitrary B⟩ ⟨a', arbitrary B⟩)

lemma card_ne_zero_of_inhabited {α : Type*} [fintype α] [inhabited α] : 
  fintype.card α ≠ 0 :=
finset.card_ne_zero_of_mem (finset.mem_univ (arbitrary α))