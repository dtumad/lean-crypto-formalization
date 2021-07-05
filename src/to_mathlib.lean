import data.bitvec.basic
import measure_theory.probability_mass_function
import analysis.special_functions.exp_log
import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials 

import data.vector2

/-!
# Miscelanious Lemams

This file is a collection of random statements that maybe should eventually move to mathlib.
Most of these are things that could usually be "handwaved" away in proofs. 
-/

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


lemma fpow_is_O_fpow_of_le {α 𝕜 : Type*} [preorder α] [normed_field 𝕜] 
  (f : α → 𝕜)
  {a b : ℤ} (h : a ≤ b) (h' : ∀ᶠ (x : α) in filter.at_top, 1 ≤ ∥f x∥):
  (is_O (λ n, (f n) ^ a) (λ n, (f n) ^ b) filter.at_top) :=
begin
  refine is_O.of_bound 1 _,
  refine filter.sets_of_superset filter.at_top h' _,
  intros x hx,
  simp only [one_mul, normed_field.norm_fpow, set.mem_set_of_eq],
  refine fpow_le_of_le hx h,
end

lemma inv_is_O_inv_iff {α 𝕜 𝕜' : Type*} [preorder α] [normed_field 𝕜] [normed_field 𝕜']
  {l : filter α} {f : α → 𝕜} {g : α → 𝕜'}
  (hf : ∀ᶠ x in l, ∥f x∥ ≠ 0) (hg : ∀ᶠ x in l, ∥g x∥ ≠ 0) :
  is_O (λ n, (f n)⁻¹) (λ n, (g n)⁻¹) l ↔ is_O g f l :=
begin
  let hfg := filter.eventually.and hf hg,
  have hfg : ∀ᶠ x in l, 0 < ∥f x∥ ∧ 0 < ∥g x∥ := begin
    refine filter.mem_sets_of_superset hfg (λ x hx, by simpa using hx),
  end,
  simp only [is_O_iff],
  refine exists_congr (λ c, ⟨λ hc, _, λ hc, _⟩),
  {

    refine filter.mem_sets_of_superset (hc.and hfg) _,
    intros x hx,
    obtain ⟨hx, hx0⟩ := hx,
    simp_rw [ normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
      mul_one, div_le_iff hx0.1, div_mul_eq_mul_div] at hx,
    refine (one_le_div hx0.2).1 hx,
  },
  {
    refine filter.mem_sets_of_superset (hc.and hfg) _,
    intros x hx,
    simp_rw [set.mem_set_of_eq, normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
      mul_one, div_le_iff hx.2.1, div_mul_eq_mul_div],
    refine (one_le_div hx.2.2).2 hx.1,
  },
end

lemma poly_help
  {p : polynomial ℝ} (hp : 1 ≤ p.degree) (c : ℝ) :
  ∀ᶠ x in filter.at_top, c ≤ ∥p.eval x∥ :=
begin
  have := polynomial.abs_tendsto_at_top p hp,
  rw filter.tendsto_at_top at this,
  specialize this c,
  exact this,
end

lemma nat_coe_tendsto (R : Type*) [linear_ordered_ring R] [archimedean R] : 
  filter.tendsto (λ (n : ℕ), (↑n : R)) filter.at_top filter.at_top :=
begin
  refine filter.tendsto_at_top.2 (λ x, _),
  obtain ⟨m, hm⟩ := exists_nat_ge x,
  rw filter.eventually_at_top,
  refine ⟨m, λ y hy, hm.trans $ nat.cast_le.2 hy⟩,
end

lemma nat_coe_eventually_ne_zero (R : Type*) [linear_ordered_ring R] [archimedean R] :
  ∀ᶠ (x : ℕ) in filter.at_top, (x : R) ≠ 0 :=
begin
  simp only [filter.eventually_at_top, ge_iff_le, ne.def, nat.cast_eq_zero],
  exact ⟨1, λ x hx h, not_le_of_lt zero_lt_one (le_trans hx (le_of_eq h))⟩,
end

-- This is the main lemma that doesn't generalize away from ℝ
lemma real.norm_nat_coe_eventually_ge (c : ℝ) :
  ∀ᶠ (x : ℕ) in filter.at_top, c ≤ ∥(x : ℝ)∥ :=
begin
  simp,
  obtain ⟨y, hy⟩ := exists_nat_ge c,
  refine ⟨y, λ x hx, hy.trans _⟩,
  simpa,
end

@[simp]
lemma comap_nat_coe_at_top (R : Type*) [linear_ordered_ring R] [archimedean R] : 
  filter.comap (λ n, ↑n : ℕ → R) filter.at_top = 
  (filter.at_top : filter ℕ) :=
begin
  ext t,
  split,
  {
    intro h,
    rw filter.mem_comap_sets at h,
    obtain ⟨s, hs, h⟩ := h,
    rw filter.mem_at_top_sets at hs ⊢,
    obtain ⟨a, ha⟩ := hs,
    obtain ⟨b, hb⟩ := exists_nat_ge a,
    refine ⟨b, λ x hx, h _⟩,
    rw set.mem_preimage,
    refine ha x (hb.trans _),
    rw nat.cast_le,
    exact hx,
  },
  {
    intro h,
    rw filter.mem_comap_sets,
    rw filter.mem_at_top_sets at h,
    obtain ⟨a, ha⟩ := h,
    refine ⟨set.Ici ↑a, _, _⟩,
    {
      simp,
      refine ⟨↑a, λ b, id⟩,
    },
    {
      intros x hx,
      rw [set.mem_preimage, set.mem_Ici, nat.cast_le] at hx,
      refine ha x hx,
    }
  },
end

end asymptotics

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

section misc

lemma eq_zero_of_norm_fpow_eq_zero {𝕜 : Type*} [normed_field 𝕜] {x : 𝕜} {z : ℤ}
  (hx : ∥x ^ z∥ = 0) : x = 0 :=
fpow_eq_zero (norm_eq_zero.mp hx)

lemma eventually_fpow_ne_zero {α 𝕜 : Type*} [preorder α]
  [normed_linear_ordered_field 𝕜] (ι : α → 𝕜)
  (hι : ∀ᶠ (n : α) in filter.at_top, (ι n) ≠ 0) (z : ℤ) : 
  ∀ᶠ (n : α) in filter.at_top, ∥(ι n) ^ z∥ ≠ 0 :=
filter.mem_sets_of_superset hι (λ x hx, mt eq_zero_of_norm_fpow_eq_zero hx)

lemma tsum_unique {α β : Type*} [add_comm_monoid α] [topological_space α]
  [t2_space α] [decidable_eq β]
  (f : β → α) (b : β) (hf : ∀ b' ≠ b, f b' = 0) :
  tsum f = f b :=
begin
  refine (tsum_congr (λ b', _)).trans (tsum_ite_eq b (f b)),
  split_ifs with h h,
  { exact congr_arg f h },
  { exact hf _ h }
end

lemma ite_le {A : Type*} [has_le A] {a b c : A} (p : Prop) [decidable p]
  (hab : b ≤ a) (hac : c ≤ a) : ite p b c ≤ a :=
by split_ifs; assumption

-- @[simp]
-- lemma vector.prod_update_nth {G : Type} [group G] {n : ℕ}
--   (v : vector G n) (i : fin n) (g : G) :
--   (v.update_nth i g).to_list.prod = 
--     v.to_list.prod * (v.nth i)⁻¹ * g :=
-- begin
--   sorry,
-- end

-- example : Prop :=
-- begin
--   have := vector.remove_nth
-- end

-- @[simp]
-- lemma helper {G : Type} [group G] (g : G) {n : ℕ} (i : fin n)
--   (cs : vector G n) :
--   (vector.of_fn (λ (j : fin n), ite (j = i) g (cs.nth j)))

-- lemma group_prod_thing {G : Type} [comm_group G] (g : G)
--   {n : ℕ} (i : fin n) (cs : vector G n) : (list.of_fn
--    (λ (j : fin n), ite (j = i) 
--     (g * cs.nth i * (list.map has_inv.inv cs.to_list).prod)
--         (cs.nth j))).prod = g :=
-- begin
--   sorry,
-- end

end misc