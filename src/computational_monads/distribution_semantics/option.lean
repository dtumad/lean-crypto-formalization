import computational_monads.distribution_semantics.prob_event

/-!
# Probabilities for Computations Over Option Type

General lemmas about probability computations involving `option`
-/

namespace distribution_semantics

variables {α β γ : Type} {spec spec' : oracle_spec}
variable [spec.finite_range]

section eval_distribution


end eval_distribution

section equiv


end equiv

section prob_event

variables (oa : oracle_comp spec (option α)) (e : set (option α))

lemma prob_event_option (e : set (option α)) : ⦃ e | oa ⦄ =
  ⦃{a | a ∈ e ∧ option.is_none a} | oa ⦄ + ⦃{ a | a ∈ e ∧ option.is_some a } | oa ⦄ :=
sorry

lemma prob_event_is_none : ⦃coe ∘ option.is_none | oa ⦄ = ⦃oa⦄ none :=
sorry

lemma prob_event_is_some : ⦃coe ∘ option.is_some | oa⦄ =
  ∑' (a : α), ⦃oa⦄ (some a) :=
sorry

end prob_event

section indep_events


end indep_events

section indep_event


end indep_event

end distribution_semantics 