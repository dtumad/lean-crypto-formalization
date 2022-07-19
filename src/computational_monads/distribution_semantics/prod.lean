import computational_monads.distribution_semantics.prob_event

/-! 
# Distributions Corresponding to Computations in Product Types

  -/

namespace distribution_semantics

variables {spec spec' : oracle_spec} {α β γ : Type}
variable [spec.finite_range]

section eval_distribution

lemma eval_distribution_prod (oa : oracle_comp spec α) (ob : oracle_comp spec β) (a : α) (b : β) :
  ⦃do {a' ← oa, b' ← ob, pure (a', b')}⦄ (a, b) = ⦃oa⦄ a * ⦃ob⦄ b :=
sorry

end eval_distribution

section prob_event

lemma eval_prob_prod_eq (oa : oracle_comp spec (α × α)) :
  ⦃λ ⟨a, a'⟩, a = a' | oa⦄ = ∑' (a₀ : α), ⦃λ ⟨a, a'⟩, a = a₀ ∧ a' = a₀ | oa⦄ :=
sorry

end prob_event

section indep_events

/-- Any collections of sets corresponding to output types of two computations
  are independent when returning the outputs of the computations in a `prod` type -/
lemma indep_events_prod (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (events₁ : set (set α)) (events₂ : set (set β)) :
  indep_events (do { a ← oa, b ← ob, return (a, b) })
    ((λ e, {x | x.1 ∈ e}) '' events₁) ((λ e, {x | x.2 ∈ e}) '' events₂) :=
sorry

end indep_events

section indep_event

/-- Any events corresponding to two computations respective output types
  are independent when returning the two outputs in a `prod` type -/
lemma indep_event_prod (e₁ : set α) (e₂ : set β)
  (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  indep_event (do { a ← oa, b ← ob, return (a, b) })
    {x | x.1 ∈ e₁} {x | x.2 ∈ e₂} :=
sorry

end indep_event

end distribution_semantics