import computational_monads.simulation_semantics.default_simulate

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

section compose

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

end compose