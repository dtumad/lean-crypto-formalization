import probability.probability_mass_function.constructions 
import data.vector.basic
import data.vector.mem
import analysis.convex.function
import analysis.convex.specific_functions

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

open_locale nnreal ennreal big_operators classical

variables {α β γ : Type*}

lemma singleton_eq_top_of_subsingleton {α : Type*} [subsingleton α] (x : α) : ({x} : set α) = ⊤ :=
set.ext (λ y, by simp only [set.mem_singleton_iff,
  eq_iff_true_of_subsingleton, set.top_eq_univ, set.mem_univ])

lemma finset.count_to_list [decidable_eq α] (s : finset α) (a : α) :
  s.to_list.count a = if a ∈ s then 1 else 0 :=
by simp only [list.count_eq_of_nodup s.nodup_to_list, finset.mem_to_list]

section tsum_prod

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

end tsum_prod

namespace ennreal

lemma to_nnreal_tsum_coe_eq {α : Type*} (f : α → ℝ≥0) :
  (∑' x, (f x : ℝ≥0∞)).to_nnreal = ∑' x, f x :=
trans (tsum_to_nnreal_eq $ λ x, ennreal.coe_ne_top) (tsum_congr $ λ x, ennreal.to_nnreal_coe)

lemma to_nnreal_sum_coe_eq {α : Type*} (f : α → ℝ≥0) (s : finset α) :
  (∑ x in s, (f x : ℝ≥0∞)).to_nnreal = ∑ x in s, f x :=
trans (to_nnreal_sum $ λ x _, ennreal.coe_ne_top)
  (finset.sum_congr rfl $ λ x _, ennreal.to_nnreal_coe)

-- SUMS
lemma sum_eq_tsum_indicator {α β : Type*} [add_comm_monoid β] [topological_space β] [t2_space β]
  (f : α → β) (s : finset α) : ∑ x in s, f x = ∑' x, set.indicator ↑s f x :=
have ∀ x ∉ s, set.indicator ↑s f x = 0,
from λ x hx, set.indicator_apply_eq_zero.2 (λ hx', (hx $ finset.mem_coe.1 hx').elim),
trans (finset.sum_congr rfl (λ x hx, symm $ set.indicator_apply_eq_self.2
  (λ hx', false.elim (hx' $ finset.mem_coe.2 hx)))) (tsum_eq_sum this).symm

end ennreal

section extract

/-- Version of `tsum_ite_eq_extract` for `add_comm_monoid` rather than `add_comm_group`.
Requires a different convergence assumption involving `function.update` -/
lemma tsum_ite_eq_extract' {α β : Type*} [topological_space α] [add_comm_monoid α] [t2_space α]
  [has_continuous_add α] {f : β → α} (b : β) (hf : summable (f.update b 0)) :
  ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
calc ∑' x, f x = ∑' x, ((ite (x = b) (f x) 0) + (ite (x = b) 0 (f x))) :
    tsum_congr (λ n, by split_ifs; simp only [zero_add, add_zero])
  ... = ∑' x, ite (x = b) (f x) 0 + ∑' x, ite (x = b) 0 (f x) :
    have (λ (b' : β), ite (b' = b) 0 (f b')) = function.update f b 0,
    from funext (λ b', symm $ f.update_apply b 0 b'),
    tsum_add ⟨ite (b = b) (f b) 0, has_sum_single b (λ b hb, if_neg hb)⟩ (this.symm ▸ hf)
  ... = (ite (b = b) (f b) 0) + ∑' x, ite (x = b) 0 (f x) :
    by { congr, exact (tsum_eq_single b (λ b' hb', if_neg hb')) }
  ... = f b + ∑' x, ite (x = b) 0 (f x) :
    by { congr, exact (if_pos rfl) }

lemma nnreal.tsum_ite_eq_extract {f : β → ℝ≥0} (hf : summable f) (b : β) :
  ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
begin
  refine tsum_ite_eq_extract' b (nnreal.summable_of_le (λ b', _) hf),
  rw [function.update_apply],
  split_ifs; simp only [zero_le', le_rfl]
end

lemma ennreal.tsum_ite_eq_extract {f : β → ℝ≥0∞} (hf : summable f) (b : β) :
  ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
tsum_ite_eq_extract' b ennreal.summable

end extract

section option

lemma nnreal.tsum_option {f : option α → ℝ≥0} (hf : summable f) :
  tsum f = f none + ∑' (a : α), f (some a) :=
calc ∑' (x : option α), f x
  = f none + ∑' (x : option α), ite (x = none) 0 (f x) : begin
    convert @nnreal.tsum_ite_eq_extract (option α) f hf none,
    ext x, split_ifs,
    refl, refl,
  end
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

end option