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

variables {α β γ : Type} {spec spec' : oracle_spec} (oa oa' : oracle_comp spec α)

section ite

variables (p : Prop) [decidable p]

@[simp] lemma mem_support_ite_iff (x : α) : x ∈ (if p then oa else oa').support ↔
  (p ∧ x ∈ oa.support) ∨ (¬ p ∧ x ∈ oa'.support) :=
by split_ifs with h; simp only [h, true_and, not_true, false_and,
  or_false, false_and, not_false_iff, true_and, false_or]

@[simp] lemma mem_fin_support_ite_iff (x : α) : x ∈ (if p then oa else oa').support ↔
  (p ∧ x ∈ oa.fin_support) ∨ (¬ p ∧ x ∈ oa'.fin_support) :=
by simp only [mem_fin_support_iff_mem_support, mem_support_ite_iff]

@[simp] lemma eval_dist_ite : ⁅if p then oa else oa'⁆ = if p then ⁅oa⁆ else ⁅oa'⁆ :=
by split_ifs; refl

@[simp] lemma eval_dist_ite_apply (x : α) : ⁅= x | if p then oa else oa'⁆ =
  if p then ⁅= x | oa⁆ else ⁅= x | oa'⁆ := by split_ifs; refl

@[simp] lemma prob_event_ite (e : set α) : ⁅e | if p then oa else oa'⁆ =
  if p then ⁅e | oa⁆ else ⁅e | oa'⁆ := by split_ifs; refl

lemma dist_equiv_ite_iff (oa'' : oracle_comp spec' α) :
  (oa'' ≃ₚ if p then oa else oa') ↔ (p → oa'' ≃ₚ oa) ∧ (¬ p → oa'' ≃ₚ oa') :=
by split_ifs with hp; simp [hp]

@[simp_dist_equiv] lemma ite_dist_equiv : (if p then oa else oa') ≃ₚ
  do {x ← oa, x' ← oa', if p then return x else return x'} :=
begin
  split_ifs with hp,
  { exact trans (bind_return_id_dist_equiv oa).symm (by pairwise_dist_equiv) },
  { exact trans (bind_const_dist_equiv oa oa').symm (by pairwise_dist_equiv) }
end

end ite

variables (p : α → Prop) [decidable_pred p]

section bind_ite

variables (ob ob' : α → oracle_comp spec β)

/-- Running one of two computations based on an `ite` is like running them both from the start,
and then choosing which result to take based on a final `ite` statement. -/
@[simp_dist_equiv] lemma bind_ite_dist_equiv : (oa >>= λ x, if p x then ob x else ob' x) ≃ₚ
  do {x ← oa, y ← ob x, y' ← ob' x, return (if p x then y else y')} :=
begin
  pairwise_dist_equiv,
  split_ifs,
  { exact trans (bind_return_id_dist_equiv (ob x)).symm (by pairwise_dist_equiv) },
  { exact trans (by pairwise_dist_equiv) (bind_const_dist_equiv _ _).symm }
end

/-- The support of binding a computation `oa` to an `ite` of two independent computations,
that may both depend on the output oa `oa`, is the union of the support of the two paths. -/
@[simp] lemma support_bind_ite : (do {x ← oa, if p x then ob x else ob' x}).support =
  (⋃ x ∈ {x ∈ oa.support | p x}, (ob x).support) ∪
    (⋃ x ∈ {x ∈ oa.support | ¬ p x}, (ob' x).support) :=
set.ext (λ x, by simp only [mem_support_bind_iff, set.mem_Union, set.mem_union, exists_prop,
  set.mem_sep_iff, ← exists_or_distrib, and_assoc, ← and_or_distrib_left, mem_support_ite_iff])

/-- The probability of getting a certain output from a computation `oa` bound to an `ite`
can be written as a sum over outputs where the predicate is true and where it's false. -/
@[simp] lemma eval_dist_bind_ite (y : β) : ⁅= y | do {x ← oa, if p x then ob x else ob' x}⁆ =
  (∑' x, if p x then ⁅= x | oa⁆ * ⁅= y | ob x⁆ else 0) +
    (∑' x, if ¬ p x then ⁅= x | oa⁆ * ⁅= y | ob' x⁆ else 0) :=
begin
  rw [← ennreal.tsum_add, eval_dist_bind_apply_eq_tsum],
  exact tsum_congr (λ x, by split_ifs with hx; simp only [zero_add, add_zero]),
end

end bind_ite

section bind_ite_const_left

variables (ob : oracle_comp spec β) (ob' : α → oracle_comp spec β) (y : β)

/-- Version of `eval_dist_bind_ite_const` when only the left computation is constant -/
@[simp] lemma eval_dist_bind_ite_const_left : ⁅= y | do {x ← oa, if p x then ob else ob' x}⁆ =
  ⁅p | oa⁆ * ⁅= y | ob⁆ + (∑' x, if ¬ p x then ⁅= x | oa⁆ * ⁅= y | ob' x⁆ else 0) :=
begin
  simp_rw [prob_event_eq_tsum_ite, eval_dist_bind_apply_eq_tsum,
    ← ennreal.tsum_mul_right, ← ennreal.tsum_add],
  exact tsum_congr (λ x, by split_ifs with h; simp only [zero_mul, zero_add, add_zero])
end

end bind_ite_const_left

section bind_ite_const_right

variables (ob : α → oracle_comp spec β) (ob' : oracle_comp spec β) (y : β)

/-- Version of `support_bind_ite_const` when only the right computation is constant -/
@[simp] lemma support_bind_ite_const_right (h : ∃ x ∈ oa.support, ¬ p x) :
  (do {x ← oa, if p x then ob x else ob'}).support =
  (⋃ x ∈ {x ∈ oa.support | p x}, (ob x).support) ∪ ob'.support :=
begin
  rw [support_bind_ite],
  refine congr_arg (λ x, _ ∪ x) _,
  ext x,
  simp at ⊢ h,
  refine λ _, h,
end
-- set.ext (λ x, by simp only [mem_support_bind_iff, set.mem_Union, set.mem_union, exists_prop,
--   set.mem_sep_iff, ← exists_or_distrib, and_assoc, ← and_or_distrib_left, mem_support_ite_iff])

/-- Version of `eval_dist_bind_ite_const` when only the right computation is constant -/
@[simp] lemma eval_dist_bind_ite_const_right : ⁅= y | do {x ← oa, if p x then ob x else ob'}⁆ =
  (∑' x, if p x then ⁅= x | oa⁆ * ⁅= y | ob x⁆ else 0) + (1 - ⁅p | oa⁆) * ⁅= y | ob'⁆ :=
begin
  simp_rw [← prob_event_not, prob_event_eq_tsum_ite, eval_dist_bind_apply_eq_tsum,
    ← ennreal.tsum_mul_right, ← ennreal.tsum_add],
  exact tsum_congr (λ x, by split_ifs with h; simp only [zero_mul, zero_add, add_zero])
end

end bind_ite_const_right

section bind_ite_const

variables (ob ob' : oracle_comp spec β) (y : β)

/-- Simplified version of `eval_dist_bind_ite` when only the predicate depends on the
result of the first computation, and the other two computations are constant. -/
@[simp] lemma eval_dist_bind_ite_const : ⁅= y | do {x ← oa, if p x then ob else ob'}⁆ =
  ⁅p | oa⁆ * ⁅= y | ob⁆ + (1 - ⁅p | oa⁆) * ⁅= y | ob'⁆ :=
begin
  simp_rw [← prob_event_not, prob_event_eq_tsum_ite, eval_dist_bind_apply_eq_tsum,
    ← ennreal.tsum_mul_right, ← ennreal.tsum_add],
  exact tsum_congr (λ x, by split_ifs with h; simp only [zero_mul, zero_add, add_zero]),
end

example : ⁅= y | do {x ← oa, if p x then ob else ob'}⁆ =
  ⁅p | oa⁆ * ⁅= y | ob⁆ + (1 - ⁅p | oa⁆) * ⁅= y | ob'⁆ :=
by simp [-eval_dist_bind] -- TODO: this isn't a great thing (maybe `prob_eq` definition?)

end bind_ite_const

section bind_ite_return

variables (f g : α → β) (y : β)

/-- Simplified version of `support_bind_ite` when the final computations are returns. -/
@[simp] lemma support_bind_ite_return :
  (do {x ← oa, if p x then return (f x) else return (g x)}).support =
    (f '' {x ∈ oa.support | p x}) ∪ (g '' {x ∈ oa.support | ¬ p x}) :=
(support_bind_ite oa p _ _).trans (by congr; exact set.ext (λ x, by simp only [@eq_comm _ x,
  support_return, set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_image]))

@[simp] lemma fin_support_bind_ite_return [decidable_eq β] :
  (do {x ← oa, if p x then return (f x) else return (g x)}).fin_support =
    ((oa.fin_support.filter p).image f) ∪ ((oa.fin_support.filter (not ∘ p)).image g) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind_ite_return,
  finset.coe_union, finset.coe_image, finset.coe_filter, coe_fin_support_eq_support]

lemma eval_dist_bind_ite_return [decidable_eq β] :
  ⁅do {x ← oa, if p x then return (f x) else return (g x)}⁆ y =
    (∑' x, if p x ∧ y = f x then ⁅oa⁆ x else 0) + (∑' x, if ¬ p x ∧ y = g x then ⁅oa⁆ x else 0) :=
begin
  simp [ite_and, ← tsum_add, -eval_dist_ite],
  exact tsum_congr (λ x, by split_ifs; simp only [zero_add, add_zero])
end

end bind_ite_return

end oracle_comp