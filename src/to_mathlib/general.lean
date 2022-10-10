import probability.probability_mass_function.constructions 
import data.vector.basic
import data.vector.mem
import analysis.convex.function
import analysis.convex.specific_functions

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

open_locale measure_theory nnreal ennreal big_operators

variables {α β γ : Type*} {n : ℕ}

@[simp]
lemma singleton_eq_top_of_subsingleton {α : Type*} [subsingleton α] (x : α) : ({x} : set α) = ⊤ :=
set.ext (λ y, by simp only [set.mem_singleton_iff,
  eq_iff_true_of_subsingleton, set.top_eq_univ, set.mem_univ])

lemma finset.count_to_list [decidable_eq α] (s : finset α) (a : α) :
  s.to_list.count a = if a ∈ s then 1 else 0 :=
by simp only [list.count_eq_of_nodup s.nodup_to_list, finset.mem_to_list]

section option

lemma option.set_eq_union_is_none_is_some {α : Type*} (s : set (option α)) :
  s = {x ∈ s | x.is_none} ∪ {x ∈ s | x.is_some} :=
begin
  refine set.ext (λ x, ⟨λ hx, _, λ hx, _⟩),
  { cases x with x; simp [hx], },
  { exact or.rec_on hx (λ hx', hx'.1) (λ hx', hx'.1) }
end

lemma option.disjoint_is_none_is_some {α : Type*} (s : set (option α)) :
  disjoint {x ∈ s | option.is_none x} {x ∈ s | option.is_some x} :=
begin
  refine le_of_eq (set.eq_empty_of_forall_not_mem $ option.rec _ _),
  { exact λ hx, by simpa using hx.right },
  { refine λ hx, by simp }
end

end option

section tsum

lemma tsum_prod_eq_tsum_snd {α β γ : Type*} [add_comm_monoid α] [topological_space α] [t2_space α]
  {f : β × γ → α} (b : β) (h : ∀ b' ≠ b, ∀ c, f (b', c) = 0) :
  ∑' (x : β × γ), f x = ∑' (c : γ), f (b, c) :=
begin
  sorry,
end

lemma tsum_prod_eq_tsum_fst {α β γ : Type*} [add_comm_monoid α] [topological_space α] [t2_space α]
  {f : β × γ → α} (c : γ) (h : ∀ c' ≠ c, ∀ b, f (b, c') = 0) :
  ∑' (x : β × γ), f x = ∑' (b : β), f (b, c) :=
begin
  refine tsum_eq_tsum_of_ne_zero_bij (λ b, (b.1, c)) (λ x x' hx, _) (λ x hx, _) (λ x, rfl),
  { simpa only [eq_self_iff_true, and_true, prod.eq_iff_fst_eq_snd_eq] using hx },
  { cases x with b c',
    have hc : c' = c := by_contra (λ hc, hx $ h c' hc b),
    refine ⟨⟨b, by rwa [function.mem_support, ← hc]⟩, _⟩,
    simp only [prod.mk.inj_iff, eq_self_iff_true, true_and, hc] }
end

namespace ennreal

open_locale classical

-- TSUMS
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

-- `to_nnreal_tsum`
lemma to_nnreal_tsum {α : Type*} {f : α → ℝ≥0∞} (hf : ∀ x, f x ≠ ⊤) :
  (∑' x, f x).to_nnreal = ∑' x, (f x).to_nnreal :=
(to_nnreal_tsum_eq f).trans (if_neg (not_exists.2 hf))

lemma to_nnreal_tsum_coe {α : Type*} {f : α → ℝ≥0} :
  (∑' x, (f x : ℝ≥0∞)).to_nnreal = ∑' x, f x :=
trans (to_nnreal_tsum $ λ x, ennreal.coe_ne_top) (tsum_congr $ λ x, ennreal.to_nnreal_coe)

lemma to_real_tsum {α : Type*} {f : α → ℝ≥0∞} (hf : ∀ x, f x ≠ ⊤) :
  (∑' x, f x).to_real = ∑' x, (f x).to_real :=
by simp_rw [ennreal.to_real, to_nnreal_tsum hf, nnreal.coe_tsum]




-- SUMS
lemma sum_eq_tsum_indicator {α β : Type*} [add_comm_monoid β] [topological_space β] [t2_space β]
  (f : α → β) (s : finset α) : ∑ x in s, f x = ∑' x, set.indicator ↑s f x :=
have ∀ x ∉ s, set.indicator ↑s f x = 0,
from λ x hx, set.indicator_apply_eq_zero.2 (λ hx', (hx $ finset.mem_coe.1 hx').elim),
trans (finset.sum_congr rfl (λ x hx, symm $ set.indicator_apply_eq_self.2
  (λ hx', false.elim (hx' $ finset.mem_coe.2 hx)))) (tsum_eq_sum this).symm

lemma sum_eq_top_of_eq_top {α : Type*} {f : α → ℝ≥0∞} {s : finset α} (hf : ∃ x ∈ s, f x = ⊤) :
  ∑ x in s, f x = ⊤ :=
(sum_eq_tsum_indicator f s).trans (let ⟨x, hx, hxf⟩ := hf in ennreal.tsum_eq_top_of_eq_top
  ⟨x, trans (set.indicator_apply_eq_self.2 (λ hx', (hx' $ finset.mem_coe.2 hx).elim)) hxf⟩)

lemma to_nnreal_indicator {α : Type*} (s : set α) (f : α → ℝ≥0∞) (x : α) :
  (s.indicator f x).to_nnreal = s.indicator (ennreal.to_nnreal ∘ f) x :=
begin
  simp_rw [set.indicator_apply],
  split_ifs,
  { exact rfl },
  { exact ennreal.zero_to_nnreal }
end

lemma indicator_apply_eq_top {α : Type*} (s : set α) (f : α → ℝ≥0∞) (x : α) :
  s.indicator f x = ⊤ ↔ x ∈ s ∧ f x = ⊤ :=
begin
  rw [set.indicator_apply],
  split_ifs;
  simp only [h, true_and, zero_ne_top, false_and]
end

end ennreal

/-- Version of `tsum_ite_eq_extract` for `nnreal` rather than `topological_add_group`. -/
lemma nnreal.tsum_ite_eq_extract [decidable_eq β] {f : β → ℝ≥0} (hf : summable f) (b : β) :
  ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
calc ∑' x, f x = ∑' x, ((ite (x = b) (f x) 0) + (ite (x = b) 0 (f x))) :
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
