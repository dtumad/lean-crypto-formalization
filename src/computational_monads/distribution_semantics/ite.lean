/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad

/-!
# Distribution Semantics of If-Then-Else

This file gives various lemmas for probability outcomes of various combinations
involving the `ite` operation.
-/

namespace oracle_comp

open_locale big_operators

variables {α β γ : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec α) (p : α → Prop) (f g : α → β) (x : α) (y : β)

lemma eval_dist_bind_ite_apply_eq_tsum_add_tsum [decidable_pred p] [decidable_eq β] :
  ⁅oa >>= λ a, return (if p a then f a else g a)⁆ y =
    (∑' x, ite (p x ∧ y = f x) (⁅oa⁆ x) 0) + (∑' x, ite (¬ p x ∧ y = g x) (⁅oa⁆ x) 0) :=
begin
  rw [eval_dist_bind_return_apply_eq_tsum, ← ennreal.tsum_add],
  refine tsum_congr (λ x, _),
  by_cases hpx : p x;
  simp only [hpx, if_true, true_and, not_true, false_and, if_false, add_zero,
    if_false, false_and, not_false_iff, true_and, zero_add]
end

lemma eval_dist_bind_ite_apply_eq_sum_add_sum [fintype α] [decidable_pred p] [decidable_eq β] :
  ⁅oa >>= λ a, return (if p a then f a else g a)⁆ y =
    (∑ x, ite (p x ∧ y = f x) (⁅oa⁆ x) 0) + (∑ x, ite (¬ p x ∧ y = g x) (⁅oa⁆ x) 0) :=
begin
  rw [eval_dist_bind_return_apply_eq_sum, ← finset.sum_add_distrib],
  refine finset.sum_congr rfl (λ x _, _),
  by_cases hpx : p x;
  simp only [hpx, if_true, true_and, not_true, false_and, if_false, add_zero,
    if_false, false_and, not_false_iff, true_and, zero_add],
end


-- TODO: This doesn't really belong in this file
@[simp] lemma support_bind_ite (oa : oracle_comp spec α) (p : α → Prop) [decidable_pred p]
  (f g : α → β) : (oa >>= λ a, return (if p a then f a else g a)).support =
  (f '' {x ∈ oa.support | p x}) ∪ (g '' {x ∈ oa.support | ¬ p x}) :=
begin
  refine set.ext (λ x, _),
  simp only [mem_support_bind_return_iff, set.mem_union,
    set.mem_image, exists_prop, set.mem_sep_iff],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨x, hx⟩ := h,
    by_cases hpx : p x,
    { rw [if_pos hpx] at hx,
      exact or.inl ⟨x, ⟨hx.1, hpx⟩, hx.2⟩ },
    { rw [if_neg hpx] at hx,
      exact or.inr ⟨x, ⟨hx.1, hpx⟩, hx.2⟩ } },
  { cases h with h h,
    { obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := h,
      exact ⟨x, hx, if_pos hx'⟩ },
    { obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := h,
      exact ⟨x, hx, if_neg hx'⟩ } }
end

@[simp] lemma fin_support_bind_ite [decidable_eq β] (oa : oracle_comp spec α)
  (p : α → Prop) [decidable_pred p] (f : α → β) (g : α → β) :
  (oa >>= λ a, return (if p a then f a else g a)).fin_support =
    ((oa.fin_support.filter p).image f) ∪ ((oa.fin_support.filter (not ∘ p)).image g) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind_ite, finset.coe_union,
  finset.coe_image, finset.coe_filter, coe_fin_support_eq_support]


end oracle_comp