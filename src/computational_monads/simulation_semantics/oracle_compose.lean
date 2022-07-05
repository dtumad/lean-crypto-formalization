import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.constructions.stateless_oracle

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

section compose

def oracle_compose (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'') :
  simulation_oracle spec spec'' :=
{ S := so.S × so'.S,
  default_state := (so.default_state, so'.default_state),
  o := λ i ⟨t, s, s'⟩, simulate so' (so.o i (t, s)) s' >>= λ ⟨⟨u, s⟩, s'⟩, return (u, s, s') }

notation so' `∘ₛ` so := oracle_compose so so'

variables (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'')

@[simp]
lemma default_state_oracle_compose :
  (so' ∘ₛ so).default_state = (so.default_state, so'.default_state) := rfl

end compose