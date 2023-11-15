/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.rw_dist_equiv

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

@[simp] lemma support_ite : (if p then oa else oa').support =
  if p then oa.support else oa'.support := by split_ifs; refl

@[simp] lemma fin_support_ite [decidable_eq α] : (if p then oa else oa').fin_support =
  if p then oa.fin_support else oa'.fin_support := by split_ifs; refl

lemma mem_support_ite_iff (x : α) : x ∈ (if p then oa else oa').support ↔
  (p ∧ x ∈ oa.support) ∨ (¬ p ∧ x ∈ oa'.support) :=
by split_ifs with h; simp only [h, true_and, not_true, false_and,
  or_false, false_and, not_false_iff, true_and, false_or]

lemma mem_fin_support_ite_iff [decidable_eq α] (x : α) : x ∈ (if p then oa else oa').support ↔
  (p ∧ x ∈ oa.fin_support) ∨ (¬ p ∧ x ∈ oa'.fin_support) :=
by simp only [mem_fin_support_iff_mem_support, mem_support_ite_iff]

@[simp] lemma eval_dist_ite : ⁅if p then oa else oa'⁆ = if p then ⁅oa⁆ else ⁅oa'⁆ :=
by split_ifs; refl

@[simp] lemma prob_output_ite (x : α) : ⁅= x | if p then oa else oa'⁆ =
  if p then ⁅= x | oa⁆ else ⁅= x | oa'⁆ := by split_ifs; refl

@[simp] lemma prob_event_ite (e : set α) : ⁅e | if p then oa else oa'⁆ =
  if p then ⁅e | oa⁆ else ⁅e | oa'⁆ := by split_ifs; refl

lemma dist_equiv_ite_iff (oa'' : oracle_comp spec' α) :
  (oa'' ≃ₚ if p then oa else oa') ↔ (p → oa'' ≃ₚ oa) ∧ (¬ p → oa'' ≃ₚ oa') :=
by split_ifs with hp; simp [hp]

@[pairwise_dist_equiv] lemma ite_dist_equiv : (if p then oa else oa') ≃ₚ
  do {x ← oa, x' ← oa', if p then return x else return x'} :=
by split_ifs with hp; by rw_dist_equiv [bind_const_dist_equiv, bind_return_dist_equiv]

end ite

variables (p : α → Prop) [decidable_pred p]

section bind_ite

variables (ob ob' : α → oracle_comp spec β) (y : β) (e : set β)

/-- Running one of two computations based on an `ite` is like running them both from the start,
and then choosing which result to take based on a final `ite` statement. -/
lemma bind_ite_dist_equiv : (oa >>= λ x, if p x then ob x else ob' x) ≃ₚ
  do {x ← oa, y ← ob x, y' ← ob' x, if p x then return y else return y'} :=
by pairwise_dist_equiv

/-- The support of binding a computation `oa` to an `ite` of two independent computations,
that may both depend on the output oa `oa`, is the union of the support of the two paths. -/
@[simp] lemma support_bind_ite : (do {x ← oa, if p x then ob x else ob' x}).support =
  (⋃ x ∈ {x ∈ oa.support | p x}, (ob x).support) ∪
    (⋃ x ∈ {x ∈ oa.support | ¬ p x}, (ob' x).support) :=
set.ext (λ x, by simp only [mem_support_bind_iff, set.mem_Union, set.mem_union, exists_prop,
  set.mem_sep_iff, ← exists_or_distrib, and_assoc, ← and_or_distrib_left, mem_support_ite_iff])

/-- The probability of getting a certain output from a computation `oa` bound to an `ite`
can be written as a sum over outputs where the predicate is true and where it's false. -/
@[simp] lemma prob_output_bind_ite (y : β) : ⁅= y | do {x ← oa, if p x then ob x else ob' x}⁆ =
  (∑' x, if p x then ⁅= x | oa⁆ * ⁅= y | ob x⁆ else 0) +
    (∑' x, if ¬ p x then ⁅= x | oa⁆ * ⁅= y | ob' x⁆ else 0) :=
begin
  rw [← ennreal.tsum_add, prob_output_bind_eq_tsum],
  exact tsum_congr (λ x, by split_ifs with hx; simp only [zero_add, add_zero]),
end

/-- The probability of an event holding after a computation `oa` bound to an `ite`
can be written as a sum over outputs where the predicate is true and where it's false. -/
@[simp] lemma prob_event_bind_ite  : ⁅e | do {x ← oa, if p x then ob x else ob' x}⁆ =
  (∑' x, if p x then ⁅= x | oa⁆ * ⁅e | ob x⁆ else 0) +
    (∑' x, if ¬ p x then ⁅= x | oa⁆ * ⁅e | ob' x⁆ else 0) :=
begin
  rw [← ennreal.tsum_add, prob_event_bind_eq_tsum],
  exact tsum_congr (λ x, by split_ifs with hx; simp only [zero_add, add_zero]),
end

end bind_ite

section bind_ite_eq_bind

variables (ob ob' : α → oracle_comp spec β)

lemma bind_ite_dist_equiv_bind_left (h : ∀ x ∈ oa.support, p x) :
  do {x ← oa, if p x then ob x else ob' x} ≃ₚ do {x ← oa, ob x} :=
bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, dist_equiv_of_eq (if_pos (h x hx)))

lemma bind_ite_dist_equiv_bind_right (h : ∀ x ∈ oa.support, ¬ p x) :
  do {x ← oa, if p x then ob x else ob' x} ≃ₚ do {x ← oa, ob' x} :=
bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, dist_equiv_of_eq (if_neg (h x hx)))

end bind_ite_eq_bind

section bind_ite_const_left

variables (ob : oracle_comp spec β) (ob' : α → oracle_comp spec β) (y : β) (e : set β)

lemma support_bind_ite_const_left (h : ∃ x ∈ oa.support, p x) :
  (do {x ← oa, if p x then ob else ob' x}).support =
    ob.support ∪ (⋃ x ∈ {x ∈ oa.support | ¬ p x}, (ob' x).support) :=
begin
  refine trans (support_bind_ite _ _ _ _)
    (congr_arg (λ x, x ∪ (⋃ x ∈ {x ∈ oa.support | ¬ p x}, (ob' x).support)) (set.ext (λ x, _))),
  simpa using λ _, h,
end

/-- Version of `prob_output_bind_ite_const` when only the left computation is constant -/
@[simp] lemma prob_output_bind_ite_const_left : ⁅= y | do {x ← oa, if p x then ob else ob' x}⁆ =
  ⁅p | oa⁆ * ⁅= y | ob⁆ + (∑' x, if ¬ p x then ⁅= x | oa⁆ * ⁅= y | ob' x⁆ else 0) :=
by simpa only [prob_output_bind_ite, prob_event_eq_tsum_ite,
  ← ennreal.tsum_mul_right, ite_mul, zero_mul]

/-- Version of `prob_event_bind_ite_const` when only the left computation is constant -/
@[simp] lemma prob_event_bind_ite_const_left : ⁅e | do {x ← oa, if p x then ob else ob' x}⁆ =
  ⁅p | oa⁆ * ⁅e | ob⁆ + (∑' x, if ¬ p x then ⁅= x | oa⁆ * ⁅e | ob' x⁆ else 0) :=
by simpa only [prob_event_bind_ite, prob_event_eq_tsum_ite,
  ← ennreal.tsum_mul_right, ite_mul, zero_mul]

end bind_ite_const_left

section bind_ite_const_right

variables (ob : α → oracle_comp spec β) (ob' : oracle_comp spec β) (y : β) (e : set β)

/-- Version of `support_bind_ite_const` when only the right computation is constant -/
lemma support_bind_ite_const_right (h : ∃ x ∈ oa.support, ¬ p x) :
  (do {x ← oa, if p x then ob x else ob'}).support =
    (⋃ x ∈ {x ∈ oa.support | p x}, (ob x).support) ∪ ob'.support :=
trans (support_bind_ite _ _ _ _) (congr_arg (λ x,
  (⋃ x ∈ {x ∈ oa.support | p x}, (ob x).support) ∪ x) (set.ext (λ x, by simpa using λ _, h)))

/-- Version of `prob_output_bind_ite_const` when only the right computation is constant -/
@[simp] lemma prob_output_bind_ite_const_right : ⁅= y | do {x ← oa, if p x then ob x else ob'}⁆ =
  (∑' x, if p x then ⁅= x | oa⁆ * ⁅= y | ob x⁆ else 0) + (1 - ⁅p | oa⁆) * ⁅= y | ob'⁆ :=
by {rw ← prob_event_not, simpa only [prob_output_bind_ite, prob_event_eq_tsum_ite,
  ← ennreal.tsum_mul_right, ite_mul, zero_mul] }

/-- Version of `prob_event_bind_ite_const` when only the right computation is constant -/
@[simp] lemma prob_event_bind_ite_const_right : ⁅e | do {x ← oa, if p x then ob x else ob'}⁆ =
  (∑' x, if p x then ⁅= x | oa⁆ * ⁅e | ob x⁆ else 0) + (1 - ⁅p | oa⁆) * ⁅e | ob'⁆ :=
by {rw ← prob_event_not, simpa only [prob_event_bind_ite, prob_event_eq_tsum_ite,
  ← ennreal.tsum_mul_right, ite_mul, zero_mul] }

end bind_ite_const_right

section bind_ite_const

variables (ob ob' : oracle_comp spec β) (y : β) (e : set β)

@[simp] lemma support_bind_ite_const (h : ∃ x ∈ oa.support, p x) (h' : ∃ x ∈ oa.support, ¬ p x) :
  (do {x ← oa, if p x then ob else ob'}).support = ob.support ∪ ob'.support :=
begin
  refine trans (support_bind_ite _ _ _ _) _,
  congr' 1,
  { ext x, simpa using λ _, h },
  { ext x, simpa using λ _, h' }
end

/-- Simplified version of `prob_output_bind_ite` when only the predicate depends on the
result of the first computation, and the other two computations are constant. -/
@[simp] lemma prob_output_bind_ite_const : ⁅= y | do {x ← oa, if p x then ob else ob'}⁆ =
  ⁅p | oa⁆ * ⁅= y | ob⁆ + (1 - ⁅p | oa⁆) * ⁅= y | ob'⁆ :=
begin
  simp_rw [← prob_event_not, prob_event_eq_tsum_ite, prob_output_bind_eq_tsum,
    ← ennreal.tsum_mul_right, ← ennreal.tsum_add],
  exact tsum_congr (λ x, by split_ifs with h; simp only [zero_mul, zero_add, add_zero]),
end

/-- Simplified version of `prob_event_bind_ite` when only the predicate depends on the
result of the first computation, and the other two computations are constant. -/
@[simp] lemma prob_event_bind_ite_const : ⁅e | do {x ← oa, if p x then ob else ob'}⁆ =
  ⁅p | oa⁆ * ⁅e | ob⁆ + (1 - ⁅p | oa⁆) * ⁅e | ob'⁆ :=
begin
  rw [prob_event_bind_ite_const_left, ← prob_event_not],
  refine congr_arg (λ x, _ + x) _,
  simpa only [prob_event_eq_tsum_ite, ← ennreal.tsum_mul_right, ite_mul, zero_mul]
end

end bind_ite_const

section bind_ite_return

variables (f g : α → β) (y : β)

/-- Simplified version of `support_bind_ite` when the final computations are returns. -/
@[simp] lemma support_bind_ite_return :
  (do {x ← oa, if p x then return (f x) else return (g x)}).support =
    (f '' {x ∈ oa.support | p x}) ∪ (g '' {x ∈ oa.support | ¬ p x}) :=
(support_bind_ite oa p _ _).trans (by congr; exact set.ext (λ x, by simp only [@eq_comm _ x,
  support_return, set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_image]))

@[simp] lemma fin_support_bind_ite_return [decidable_eq α] [decidable_eq β] :
  (do {x ← oa, if p x then return (f x) else return (g x)}).fin_support =
    ((oa.fin_support.filter p).image f) ∪ ((oa.fin_support.filter (not ∘ p)).image g) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind_ite_return,
  finset.coe_union, finset.coe_image, finset.coe_filter, coe_fin_support_eq_support]

lemma prob_output_bind_ite_return [decidable_eq β] :
  ⁅= y | do {x ← oa, if p x then return (f x) else return (g x)}⁆ =
    (∑' x, if p x ∧ y = f x then ⁅= x | oa⁆ else 0) +
      (∑' x, if ¬ p x ∧ y = g x then ⁅= x | oa⁆ else 0) :=
by simp only [ite_and, prob_output_bind_ite, prob_output_return, mul_boole]

end bind_ite_return

section map_ite

variables (f : α → β)

@[pairwise_dist_equiv] lemma map_ite_dist_equiv (p : Prop) [decidable p] :
  f <$> (if p then oa else oa') ≃ₚ
    if p then f <$> oa else f <$> oa' := by split_ifs; refl

@[simp] lemma support_map_ite (p : Prop) [decidable p] :
  (f <$> if p then oa else oa').support =
    if p then (f <$> oa).support else (f <$> oa').support := by split_ifs; refl

@[simp] lemma fin_support_map_ite [decidable_eq β] (p : Prop) [decidable p] :
  (f <$> if p then oa else oa').fin_support =
    if p then (f <$> oa).fin_support else (f <$> oa').fin_support := by split_ifs; refl

@[simp] lemma eval_dist_map_ite (p : Prop) [decidable p] :
  ⁅f <$> if p then oa else oa'⁆ =
    if p then ⁅f <$> oa⁆ else ⁅f <$> oa'⁆ := by split_ifs; refl

@[simp] lemma prob_output_map_ite (p : Prop) [decidable p] (y : β) :
  ⁅= y | f <$> if p then oa else oa'⁆ =
    if p then ⁅= y | f <$> oa⁆ else ⁅= y | f <$> oa'⁆ := by split_ifs; refl

@[simp] lemma prob_event_map_ite (p : Prop) [decidable p] (e : set β) :
  ⁅e | f <$> if p then oa else oa'⁆ =
    if p then ⁅e | f <$> oa⁆ else ⁅e | f <$> oa'⁆ := by split_ifs; refl

end map_ite

end oracle_comp