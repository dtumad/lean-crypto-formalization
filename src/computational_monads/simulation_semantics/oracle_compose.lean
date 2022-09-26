import computational_monads.simulation_semantics.default_simulate

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type} {S S' : Type}

namespace sim_oracle

def oracle_compose (so : sim_oracle spec spec' S)
  (so' : sim_oracle spec' spec'' S') : sim_oracle spec spec'' (S × S') :=
{ default_state := (so.default_state, so'.default_state),
  o := λ i x, simulate so' (so i (x.1, x.2.1)) x.2.2 >>= λ u_s, pure (u_s.1.1, u_s.1.2, u_s.2) }

notation so' `∘ₛ` so := oracle_compose so so'

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec' spec'' S')

@[simp]
lemma default_state_oracle_compose :
  (so' ∘ₛ so).default_state = (so.default_state, so'.default_state) := rfl

lemma oracle_compose_apply_index (i : spec.ι) (s : S × S') : (so' ∘ₛ so) i =
  λ x, simulate so' (so i (x.1, x.2.1)) x.2.2 >>= λ u_s, pure (u_s.1.1, u_s.1.2, u_s.2) := rfl

section support

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_dist

end eval_dist

section equiv

end equiv

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end sim_oracle