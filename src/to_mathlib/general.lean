import probability.probability_mass_function.constructions 
import data.vector.basic
import data.vector.mem
import analysis.convex.function
import analysis.convex.specific_functions

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

open_locale measure_theory nnreal ennreal classical big_operators

variables {α β γ : Type*} {n : ℕ}

lemma tsum_eq_sum_univ {α β : Type*} [fintype α] [topological_space β]
  [add_comm_monoid β] [t2_space β] (f : α → β) :
  ∑' (x : α), f x = ∑ x, f x :=
tsum_eq_sum (λ b hb, false.elim (hb $ finset.mem_univ b))

lemma option.set_eq_union_is_none_is_some {α : Type*} (s : set (option α)) :
  s = {x ∈ s | x.is_none} ∪ {x ∈ s | x.is_some} :=
begin
  refine set.ext (λ x, ⟨λ hx, _, λ hx, _⟩),
  { cases x with x;
    simp only [hx, set.mem_union_eq, set.mem_sep_eq, option.is_none_some,
      option.is_none_none, coe_sort_ff, and_false, true_and, option.is_some_some,
        coe_sort_tt, and_self, false_or, true_or, or_false] },
  { exact or.rec_on hx (λ hx', hx'.1) (λ hx', hx'.1) }
end

lemma option.disjoint_is_none_is_some {α : Type*} (s : set (option α)) :
  disjoint {x ∈ s | option.is_none x} {x ∈ s | option.is_some x} :=
begin
  refine le_of_eq (set.eq_empty_of_forall_not_mem $ option.rec _ _),
  { exact λ hx, by simpa only [set.mem_sep_eq, option.is_some_none,
      coe_sort_ff, and_false] using hx.right },
  { refine λ hx, by simp only [set.inf_eq_inter, set.mem_inter_eq, set.mem_sep_eq,
    option.is_none_some, coe_sort_ff, and_false, false_and, not_false_iff] }
end

-- NOTE: PR opened for this
section list_like

lemma multiset.quot_mk_ne_zero (l : list α) (hl : ¬ l.empty) : ↑l ≠ (0 : multiset α) :=
mt ((list.empty_iff_eq_nil).2 ∘ (multiset.coe_eq_zero l).1) hl

@[simp] lemma vector.to_list_nonempty (v : vector α (n + 1)) : ¬ v.to_list.empty :=
by simp only [vector.empty_to_list_eq_ff, coe_sort_ff, not_false_iff]

end list_like

-- NOTE: Pull request opened for this
section sums

lemma real.pow_sum_div_card_le_sum_pow (s : finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
  (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, (f x) ^ (n + 1) :=
begin
  by_cases hs : s = ∅,
  { simp only [hs, finset.sum_empty, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_div] },
  { have hs₀ : s.card ≠ 0 := hs ∘ finset.card_eq_zero.1,
    have hs' : (s.card : ℝ) ≠ 0 := (nat.cast_ne_zero.2 hs₀),
    have hs'' : 0 < (s.card : ℝ) := nat.cast_pos.2 (nat.pos_of_ne_zero hs₀),
    suffices : (∑ x in s, f x / s.card) ^ (n + 1) ≤ ∑ x in s, (f x ^ (n + 1) / s.card),
    by rwa [← finset.sum_div, ← finset.sum_div, div_pow, pow_succ' (s.card : ℝ),
        ← div_div, div_le_iff hs'', div_mul, div_self hs', div_one] at this,
    have := @convex_on.map_sum_le ℝ ℝ ℝ _ _ _ _ _ _ _ (set.Ici 0) (λ x, x ^ (n + 1)) s
      (λ _, 1 / s.card) (coe ∘ f) (convex_on_pow (n + 1)) _ _ (λ i hi, set.mem_Ici.2 (hf i)),
    { simpa only [inv_mul_eq_div, one_div, algebra.id.smul_eq_mul] using this },
    { simp only [one_div, inv_nonneg, nat.cast_nonneg, implies_true_iff] },
    { simpa only [one_div, finset.sum_const, nsmul_eq_mul] using mul_inv_cancel hs' }}
end

lemma nnreal.pow_sum_div_card_le_sum_pow (s : finset α) (f : α → ℝ≥0) (n : ℕ) :
  (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, (f x) ^ (n + 1) :=
by simpa [← nnreal.coe_le_coe, nnreal.coe_sum] using
  real.pow_sum_div_card_le_sum_pow s (coe ∘ f) (λ _, nnreal.coe_nonneg _) n

end sums

section ennreal

lemma ennreal.to_nnreal_eq_to_nnreal_iff (x y : ℝ≥0∞) :
  x.to_nnreal = y.to_nnreal ↔ x = y ∨ (x = 0 ∧ y = ⊤) ∨ (x = ⊤ ∧ y = 0) :=
begin
  cases x,
  { simp only [@eq_comm ℝ≥0 _ y.to_nnreal, @eq_comm ℝ≥0∞ _ y, ennreal.to_nnreal_eq_zero_iff,
      ennreal.none_eq_top, ennreal.top_to_nnreal, ennreal.top_ne_zero, false_and, eq_self_iff_true,
        true_and, false_or, or_comm (y = ⊤)] },
  { cases y; simp }
end

lemma ennreal.to_real_eq_to_real_iff (x y : ℝ≥0∞) :
  x.to_real = y.to_real ↔ x = y ∨ (x = 0 ∧ y = ⊤) ∨ (x = ⊤ ∧ y = 0) :=
by simp only [ennreal.to_real, nnreal.coe_eq, ennreal.to_nnreal_eq_to_nnreal_iff]

lemma ennreal.to_nnreal_eq_to_nnreal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
  x.to_nnreal = y.to_nnreal ↔ x = y :=
by simp only [ennreal.to_nnreal_eq_to_nnreal_iff x y, hx, hy, and_false, false_and, or_false]

lemma ennreal.to_real_eq_to_real_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
  x.to_real = y.to_real ↔ x = y :=
by simp only [ennreal.to_real, nnreal.coe_eq, ennreal.to_nnreal_eq_to_nnreal_iff' hx hy]

lemma ennreal.to_nnreal_eq_one_iff (x : ℝ≥0∞) : x.to_nnreal = 1 ↔ x = 1 :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  cases x,
  { exact false.elim (zero_ne_one $ ennreal.top_to_nnreal.symm.trans h) },
  { exact congr_arg _ h }
end

lemma ennreal.to_real_eq_one_iff (x : ℝ≥0∞) : x.to_real = 1 ↔ x = 1 :=
by rw [ennreal.to_real, nnreal.coe_eq_one, ennreal.to_nnreal_eq_one_iff]

section tsum

namespace ennreal

lemma to_nnreal_tsum_eq {α : Type*} (f : α → ℝ≥0∞) :
  (∑' x, f x).to_nnreal = if ∃ x, f x = ⊤ then 0 else ∑' x, (f x).to_nnreal :=
begin
  split_ifs with hf,
  { exact (to_nnreal_eq_zero_iff _).2 (or.inr (ennreal.tsum_eq_top_of_eq_top hf)) },
  { rw [nnreal.tsum_eq_to_nnreal_tsum],
    have : ∀ x, f x ≠ ⊤ := not_exists.1 hf,
    exact congr_arg ennreal.to_nnreal (tsum_congr $ λ x, (coe_to_nnreal (this x)).symm) }
end

lemma to_real_tsum_eq {α : Type*} (f : α → ℝ≥0∞) :
  (∑' x, f x).to_real = if ∃ x, f x = ⊤ then 0 else ∑' x, (f x).to_real :=
calc (∑' x, f x).to_real = ↑((∑' x, f x).to_nnreal) : rfl
  ... = ↑(ite (∃ x, f x = ⊤) 0 (∑' x, (f x).to_nnreal)) : congr_arg coe (to_nnreal_tsum_eq f)
  ... = ite (∃ x, f x = ⊤) 0 ↑(∑' x, (f x).to_nnreal) : by rw [apply_ite coe, nonneg.coe_zero]
  ... = ite (∃ x, f x = ⊤) 0 (∑' x, (f x).to_real) : congr_arg _ nnreal.coe_tsum

lemma to_nnreal_tsum_eq_of_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∀ x, f x ≠ ⊤) :
  (∑' x, f x).to_nnreal = ∑' x, (f x).to_nnreal :=
(to_nnreal_tsum_eq f).trans (if_neg (not_exists.2 hf))

lemma to_real_tsum_eq_of_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∀ x, f x ≠ ⊤) :
  (∑' x, f x).to_real = ∑' x, (f x).to_real :=
by simp_rw [ennreal.to_real, to_nnreal_tsum_eq_of_ne_top hf, nnreal.coe_tsum]

end ennreal

/-- Version of `tsum_ite_eq_extract` for `nnreal` rather than `topological_add_group`. -/
lemma nnreal.tsum_ite_eq_extract [decidable_eq β] {f : β → ℝ≥0} (hf : summable f) (b : β) :
  ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
calc ∑' x, f x
  = ∑' x, ((ite (x = b) (f x) 0) + (ite (x = b) 0 (f x))) :
    tsum_congr (λ n, by split_ifs; simp only [zero_add, add_zero])
  ... = ∑' x, ite (x = b) (f x) 0 + ∑' x, ite (x = b) 0 (f x) :
    by refine tsum_add (nnreal.summable_of_le (λ b', _) hf) (nnreal.summable_of_le (λ b', _) hf);
      split_ifs; simp only [le_rfl, zero_le']
  ... = (ite (b = b) (f b) 0) + ∑' x, ite (x = b) 0 (f x) :
    by { congr, exact (tsum_eq_single b (λ b' hb', if_neg hb')) }
  ... = f b + ∑' x, ite (x = b) 0 (f x) :
    by { congr, exact (if_pos rfl) }

lemma nnreal.tsum_option [decidable_eq α] {f : option α → ℝ≥0} (hf : summable f) :
  tsum f = f none + ∑' (a : α), f (some a) :=
calc ∑' (x : option α), f x
  = f none + ∑' (x : option α), ite (x = none) 0 (f x) : nnreal.tsum_ite_eq_extract hf none
  ... = f none + ∑' (a : α), f (some a) : begin
    refine congr_arg (λ x, f none + x) (tsum_eq_tsum_of_ne_zero_bij (λ a, some a.1) _ _ _),
    { simp only [subtype.val_eq_coe, imp_self, set_coe.forall, implies_true_iff] },
    { simp only [function.support_subset_iff, ne.def, ite_eq_left_iff, not_forall, exists_prop,
        set.mem_range, set_coe.exists, function.mem_support, and_imp],
      intros x hx hfx,
      cases x with a,
      { exact false.elim (hx rfl) },
      { exact ⟨a, hfx, rfl⟩ } },
    { simp only [subtype.val_eq_coe, if_false, eq_self_iff_true, implies_true_iff] }
end

end tsum

end ennreal