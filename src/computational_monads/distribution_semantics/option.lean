/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.prob_event

/-!
# Probabilities for Computations Over Option Type

General lemmas about probability computations involving `option`
-/

namespace distribution_semantics

variables {α β γ : Type} {spec spec' : oracle_spec}
variable [spec.finite_range]

section eval_dist


end eval_dist

section prob_event

variables (oa : oracle_comp spec (option α)) (e : set (option α))

lemma prob_event_option [decidable_eq α] (e : set (option α)) :
  ⁅e | oa⁆ = (e.indicator ⁅oa⁆ none) + ∑' (a : α), e.indicator ⁅oa⁆ (some a) :=
(prob_event_eq_tsum_indicator oa e).trans (ennreal.tsum_option _)

lemma prob_event_is_none : ⁅λ x, x.is_none | oa⁆ = ⁅oa⁆ none :=
prob_event_eq_eval_dist oa _ option.is_none_none
  (λ x hx hx', (hx $ option.eq_none_of_is_none hx').elim)

lemma prob_event_is_some [decidable_eq α] : ⁅λ x, x.is_some | oa⁆ = ∑' (a : α), ⁅oa⁆ (some a) :=
let e : set (option α) := λ x, x.is_some in
calc ⁅e | oa⁆
  = e.indicator ⁅oa⁆ none + ∑' (a : α), e.indicator ⁅oa⁆ (some a) : prob_event_option oa _
  ... = 0 + ∑' (a : α), e.indicator ⁅oa⁆ (some a) : begin
    congr,
    refine set.indicator_apply_eq_zero.2 (λ h, false.elim _),
    simpa only [option.is_some_none, coe_sort_ff] using (h : none.is_some),
  end
  ... = ∑' (a : α), e.indicator ⁅oa⁆ (some a) : zero_add _
  ... = ∑' (a : α), ⁅oa⁆ (some a) : begin
    refine tsum_congr (λ a, set.indicator_apply_eq_self.2 (λ h, false.elim $ h _)),
    show ((some a).is_some : Prop),
    simp only [option.is_some_some, coe_sort_tt]
  end

end prob_event

end distribution_semantics 