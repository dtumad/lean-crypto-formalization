import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.constructions.stateless_oracle

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

section oracle_append

def oracle_append (so : simulation_oracle spec' spec)
  (so' : simulation_oracle spec'' spec) :
  simulation_oracle (spec' ++ spec'') spec :=
{ S := so.S × so'.S,
  default_state := (so.default_state, so'.default_state),
  o := λ i, match i with
  | sum.inl i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so.o i ⟨t, s.1⟩, return (u, s', s.2) }
  | sum.inr i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so'.o i ⟨t, s.2⟩, return (u, s.1, s') }
  end }

notation so `⟪++⟫` so' := oracle_append so so'

variables (so : simulation_oracle spec' spec) (so' : simulation_oracle spec'' spec)

@[simp]
lemma default_state_oracle_append :
  (so ⟪++⟫ so').default_state = (so.default_state, so'.default_state) := rfl

end oracle_append

section simulate_sides

def simulate_right {spec spec' : oracle_spec}
  (so : simulation_oracle spec' spec) :
  simulation_oracle (spec ++ spec') spec :=
identity_oracle spec ⟪++⟫ so

end simulate_sides