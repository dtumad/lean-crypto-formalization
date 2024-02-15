/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.map

/-!
# Probabilities for Computations Over Option Type

General lemmas about probability computations involving `option`.
-/

namespace oracle_comp

open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

section eval_dist


end eval_dist

section prob_output

@[simp] lemma prob_output_none_map_some (oa : oracle_comp spec α) : ⁅= none | some <$> oa⁆ = 0 :=
by simp only [prob_output_eq_zero_iff, support_map, set.mem_image, and_false, exists_false,
  not_false_iff]

@[simp] lemma prob_output_some_map_some (oa : oracle_comp spec α) (x : α) :
  ⁅= some x | some <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_of_injective _ _ (option.some_injective α)

end prob_output

section prob_event

variables (oa : oracle_comp spec (option α))

lemma prob_event_option (p : option α → Prop) :
  ⁅p | oa⁆ = (set.indicator p ⁅oa⁆ none) + ∑' (a : α), set.indicator p ⁅oa⁆ (some a) :=
(prob_event_eq_tsum_indicator' oa p).trans (ennreal.tsum_option _)

@[simp] lemma prob_event_is_none : ⁅λ x, x.is_none | oa⁆ = ⁅= none | oa⁆ :=
prob_event_eq_prob_output none option.is_none_none
  (λ x hx hx', option.eq_none_of_is_none hx')

lemma prob_event_is_none_eq_tt : ⁅λ x, x.is_none = tt | oa⁆ = ⁅= none | oa⁆ :=
by simp only [prob_event_is_none]

lemma prob_event_is_some : ⁅λ x, x.is_some | oa⁆ = ∑' x : α, ⁅= some x | oa⁆ :=
let e : set (option α) := λ x, x.is_some in
calc ⁅e | oa⁆ = e.indicator ⁅oa⁆ none + ∑' (a : α), e.indicator ⁅oa⁆ (some a) :
    prob_event_option oa _
  ... = 0 + ∑' (a : α), e.indicator ⁅oa⁆ (some a) : begin
    refine congr_arg (λ n, n + ∑' (a : α), e.indicator ⁅oa⁆ (some a)) _,
    refine set.indicator_apply_eq_zero.2 (λ h, false.elim _),
    simpa only [option.is_some_none, coe_sort_ff] using (h : none.is_some),
  end
  ... = ∑' (a : α), e.indicator ⁅oa⁆ (some a) : zero_add _
  ... = ∑' (a : α), ⁅= some a | oa⁆ : begin
    refine tsum_congr (λ a, set.indicator_apply_eq_self.2 (λ h, false.elim $ h _)),
    show ((some a).is_some : Prop),
    simp only [option.is_some_some, coe_sort_tt]
  end

lemma prob_event_is_some_eq_sum [fintype α] : ⁅λ x, x.is_some | oa⁆ = ∑ x : α, ⁅= some x | oa⁆ :=
(prob_event_is_some oa).trans (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))

lemma prob_event_is_some' (oa : oracle_comp spec α) (f : α → option β) :
  ⁅λ x, (f x).is_some | oa⁆ = ∑' y : β, ⁅= some y | f <$> oa⁆ :=
by rw [← prob_event_is_some, prob_event_map]

lemma prob_event_is_some_eq_sum' [fintype β] (oa : oracle_comp spec α) (f : α → option β) :
  ⁅λ x, (f x).is_some | oa⁆ = ∑ y : β, ⁅= some y | f <$> oa⁆ :=
(prob_event_is_some' oa f).trans (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))

lemma prob_event_ne_none_eq_tsum : ⁅(≠) none | oa⁆ = ∑' x : α, ⁅= some x | oa⁆ :=
trans (prob_event_ext' (λ x h, by rw [ne_comm, option.ne_none_iff_is_some])) (prob_event_is_some _)

lemma prob_event_ne_none_eq_sum [fintype α] : ⁅(≠) none | oa⁆ = ∑ x : α, ⁅= some x | oa⁆ :=
trans (prob_event_ne_none_eq_tsum oa) (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))

lemma prob_event_is_some_eq_one_sub_prob_output_none :
  ⁅λ x, x.is_some | oa⁆ = 1 - ⁅= none | oa⁆ :=
begin
  rw [← prob_event_is_none, ← prob_event_not],
  refine congr_arg (λ e, ⁅e | _⁆) (funext (λ b, by cases b; simp))
end

end prob_event

end oracle_comp