/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.general
import topology.algebra.infinite_sum

/-!
# Lemmas about Sums that fit better in mathlib
-/

open_locale nnreal ennreal big_operators classical

variables {α β γ : Type*}

lemma sum_eq_tsum_indicator {α β : Type*} [add_comm_monoid β] [topological_space β] [t2_space β]
  (f : α → β) (s : finset α) : ∑ x in s, f x = ∑' x, set.indicator ↑s f x :=
have ∀ x ∉ s, set.indicator ↑s f x = 0,
from λ x hx, set.indicator_apply_eq_zero.2 (λ hx', (hx $ finset.mem_coe.1 hx').elim),
(finset.sum_congr rfl (λ x hx, (set.indicator_apply_eq_self.2 $
  λ hx', (hx' $ finset.mem_coe.2 hx).elim).symm)).trans (tsum_eq_sum this).symm

-- NOTE: not going to PR this
section tsum_prod

open function set

lemma tsum_prod_eq_tsum_snd {α β γ : Type*} [add_comm_monoid α] [topological_space α] [t2_space α]
  {f : β × γ → α} (b : β) (h : ∀ c, ∀ b' ≠ b, f (b', c) = 0) :
  ∑' (x : β × γ), f x = ∑' (c : γ), f (b, c) :=
begin
  have : support f ⊆ range (λ x, (b, x)),
  { rintros ⟨b, c'⟩ hx, obtain rfl := of_not_not ((h _ _).mt hx.out), exact mem_range_self _ },
  rw [← tsum_subtype_eq_of_support_subset this, tsum_range f (prod.mk.inj_left b)]
end

lemma tsum_prod_eq_tsum_fst {α β γ : Type*} [add_comm_monoid α] [topological_space α] [t2_space α]
  {f : β × γ → α} (c : γ) (h : ∀ b, ∀ c' ≠ c, f (b, c') = 0) :
  ∑' (x : β × γ), f x = ∑' (b : β), f (b, c) :=
begin
  have : support f ⊆ range (λ x, (x, c)),
  { rintros ⟨b, c'⟩ hx, obtain rfl := of_not_not ((h _ _).mt hx.out), exact mem_range_self _ },
  rw [← tsum_subtype_eq_of_support_subset this, tsum_range f (prod.mk.inj_right c)]
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

end ennreal

section extract


/-- Version of `tsum_ite_eq_extract` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that `f.update` has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/
lemma has_sum.update' {α β : Type*} [topological_space α] [add_comm_monoid α] [t2_space α]
  [has_continuous_add α] {f : β → α} {a a' : α} (hf : has_sum f a)
  (b : β) (x : α) (hf' : has_sum (f.update b x) a') : a + x = a' + f b :=
begin
  have : ∀ b', f b' + ite (b' = b) x 0 = f.update b x b' + ite (b' = b) (f b) 0,
  { intro b',
    split_ifs with hb',
    { simpa only [function.update_apply, hb', eq_self_iff_true] using add_comm (f b) x },
    { simp only [function.update_apply, hb', if_false] } },
  have h := hf.add ((has_sum_ite_eq b x)),
  simp_rw this at h,
  exact h.unique (hf'.add (has_sum_ite_eq b (f b)))
end

/-- Version of `tsum_ite_eq_extract` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that the `ite` expression has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
lemma has_sum.ite_eq_extract' {α β : Type*} [topological_space α] [add_comm_monoid α] [t2_space α]
  [has_continuous_add α] {f : β → α} {a : α} (hf : has_sum f a)
  (b : β) (a' : α) (hf' : has_sum (λ n, ite (n = b) 0 (f n)) a') :
  a = a' + f b :=
begin
  refine (add_zero a).symm.trans (hf.update' b 0 _),
  convert hf',
  exact funext (f.update_apply b 0),  
end

/-- Version of `tsum_ite_eq_extract` for `add_comm_monoid` rather than `add_comm_group`.
Requires a different convergence assumption involving `function.update` -/
lemma tsum_ite_eq_extract' {α β : Type*} [topological_space α] [add_comm_monoid α] [t2_space α]
  [has_continuous_add α] {f : β → α} (b : β) (hf : summable (f.update b 0)) :
  ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
calc ∑' x, f x = ∑' x, ((ite (x = b) (f x) 0) + (f.update b 0 x)) :
    tsum_congr (λ n, by split_ifs; simp [function.update_apply, h])
  ... = ∑' x, ite (x = b) (f x) 0 + ∑' x, f.update b 0 x :
    tsum_add ⟨ite (b = b) (f b) 0, has_sum_single b (λ b hb, if_neg hb)⟩ (hf)
  ... = (ite (b = b) (f b) 0) + ∑' x, f.update b 0 x :
    by { congr, exact (tsum_eq_single b (λ b' hb', if_neg hb')) }
  ... = f b + ∑' x, ite (x = b) 0 (f x) :
    by simp only [function.update, eq_self_iff_true, if_true, eq_rec_constant, dite_eq_ite]

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

lemma ennreal.tsum_option (f : option α → ℝ≥0∞) :
  tsum f = f none + ∑' a, f (some a) := sorry

lemma nnreal.tsum_option {f : option α → ℝ≥0} (hf : summable f) :
  tsum f = f none + ∑' (a : α), f (some a) :=
calc ∑' (x : option α), f x
  = f none + ∑' (x : option α), ite (x = none) 0 (f x) :
  begin
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