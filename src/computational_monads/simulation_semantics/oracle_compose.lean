import computational_monads.simulation_semantics.default_simulate

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

namespace simulation_oracle

def oracle_compose (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'') :
  simulation_oracle spec spec'' :=
{ S := so.S × so'.S,
  default_state := (so.default_state, so'.default_state),
  o := λ i x, simulate so' (so.o i (x.1, x.2.1)) x.2.2 >>= λ u_s, pure (u_s.1.1, u_s.1.2, u_s.2) }

notation so' `∘ₛ` so := oracle_compose so so'

variables (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'')

@[simp]
lemma default_state_oracle_compose :
  (so' ∘ₛ so).default_state = (so.default_state, so'.default_state) := rfl

lemma oracle_compose_apply_index (i : spec.ι) (s : so.S × so'.S) : (so' ∘ₛ so).o i =
  λ x, simulate so' (so.o i (x.1, x.2.1)) x.2.2 >>= λ u_s, pure (u_s.1.1, u_s.1.2, u_s.2) := rfl

theorem simulate_oracle_compose_eq_simulate_simulate (oa : oracle_comp spec A) (s : so.S × so'.S) :
  simulate' (so' ∘ₛ so) oa s = simulate' so' (simulate' so oa s.1) s.2 :=
sorry

-- When returning the state as well can only make a statement in terms of equiv
theorem other [spec''.finite_range] (oa : oracle_comp spec A) (s : so.S × so'.S) :
  simulate (so' ∘ₛ so) oa s ≃ₚ
    do { ⟨⟨a, s⟩, s'⟩ ← (simulate so' (simulate so oa s.1) s.2), pure (a, s, s') } :=
sorry

section support

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_distribution

end eval_distribution

section equiv

end equiv

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end simulation_oracle