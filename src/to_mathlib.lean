import data.bitvec.basic
import measure_theory.probability_mass_function
import analysis.special_functions.exp_log
import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials

-- Collection of random statements that maybe should eventually move to mathlib

lemma ite_le {A : Type*} [has_le A] {a b c : A} (p : Prop) [decidable p]
  (hab : b ≤ a) (hac : c ≤ a) : ite p b c ≤ a :=
by split_ifs; assumption

section asymptotics

open asymptotics

lemma is_O_of_pow_le {α 𝕜 : Type*} [normed_field 𝕜] {l : filter α}
  {f : α → 𝕜} (hf : ∀ᶠ x in l, ∥f x∥ ≥ 1) {n m : ℕ} (hnm : n ≤ m) :
  is_O (λ x, (f x) ^ n) (λ x, (f x) ^ m) l :=
begin
  rw is_O_iff,
  refine ⟨1, filter.eventually_of_mem hf (λ x hx, _)⟩,
  simp only [one_mul, normed_field.norm_pow],
  refine pow_le_pow hx hnm,
end 

end asymptotics

def decidable_eq_of_prod_left {A B : Type*} [inhabited B] [h : decidable_eq (A × B)] : 
  decidable_eq A :=
λ a a', decidable.rec (λ h, is_false (λ h', h (prod.mk.inj_iff.mpr ⟨h', rfl⟩))) 
  (λ h, is_true (prod.mk.inj_iff.mp h).1) (h ⟨a, arbitrary B⟩ ⟨a', arbitrary B⟩)

@[simp] lemma card_bitvec {n : ℕ} : fintype.card (bitvec n) = 2 ^ n :=
by rw [card_vector n, fintype.card_bool]

section const_pmf

lemma sum_inv_fintype_card_eq_one {A : Type*} [fintype A] [inhabited A] :
  has_sum (λ (a : A), (fintype.card A : nnreal)⁻¹) 1 :=
begin
  convert has_sum_fintype (λ (a : A), (fintype.card A : nnreal)⁻¹),
  rw [finset.sum_const, nsmul_eq_mul],
  refine (div_self _).symm,
  exact nat.cast_ne_zero.2 (finset.card_ne_zero_of_mem (by simp : arbitrary A ∈ _)),
end

/-- Definition of a uniform `pmf` on a finite type -/
noncomputable def pmf.const (α : Type*) [fintype α] [inhabited α] : pmf α :=
⟨λ a, (fintype.card α : nnreal)⁻¹, sum_inv_fintype_card_eq_one⟩

@[simp] lemma pmf.const_apply {α : Type*} [fintype α] [inhabited α]
  (a : α) : pmf.const α a = (fintype.card α : nnreal)⁻¹ := rfl

lemma card_ne_zero_of_inhabited {α : Type*} [fintype α] [inhabited α] : 
  fintype.card α ≠ 0 :=
finset.card_ne_zero_of_mem (finset.mem_univ (arbitrary α))

end const_pmf

section log_exp

open real

lemma log_le_of_nonneg {x : ℝ} (hx : x ≥ 0) : log x ≤ x :=
begin
  cases lt_or_eq_of_le hx with hx' hx',
  { calc log x ≤ log (exp x) : (log_le_log hx' (exp_pos x)).mpr 
        (trans (by linarith) (add_one_le_exp_of_nonneg hx))
      ... = x : by simp },
  { simp [← hx'] }
end

lemma neg_log_le_of_nonneg {x : ℝ} (hx : x ≥ 1) : - log x ≤ x :=
calc - log x ≤ 0 : neg_nonpos.mpr $ log_nonneg hx
        ... ≤ 1 : zero_le_one
        ... ≤ x : hx

lemma one_eventually_le_log : ∀ᶠ (x : ℝ) in filter.at_top, 1 ≤ ∥real.log x∥ :=
begin
  simp only [filter.eventually_at_top, ge_iff_le],
  refine ⟨real.exp 1, λ x hx, _⟩,
  suffices : 1 ≤ real.log x,
  from real.norm_eq_abs (real.log x) ▸ le_abs.2 (or.inl this),
  rwa [← real.log_exp 1, real.log_le_log (real.exp_pos 1) (lt_of_lt_of_le (real.exp_pos 1) hx)],
end

lemma log_ge_of_ge_exp {x y : ℝ} (h : x ≥ real.exp y) : real.log x ≥ y :=
calc y = real.log (real.exp y) : (real.log_exp y).symm
      ... ≤ real.log x : (real.log_le_log (real.exp_pos y) (lt_of_lt_of_le (real.exp_pos y) h)).mpr h


end log_exp

-- lemma fpow_pos_of_pos {n : ℝ} (hn : 0 < n) (c : ℤ) : 0 < n ^ c :=
-- begin
  
-- end