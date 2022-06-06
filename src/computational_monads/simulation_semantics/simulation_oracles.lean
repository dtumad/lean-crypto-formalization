import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.stateless_oracle
import computational_monads.simulation_semantics.constructions.query_log


open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

section compose

def oracle_compose {spec spec' spec'' : oracle_spec}
  (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'') :
  simulation_oracle spec spec'' :=
{ S := so.S × so'.S,
  o := λ i ⟨t, s, s'⟩, simulate so' (so.o i (t, s)) s' >>= λ ⟨⟨u, s⟩, s'⟩, return (u, s, s') }

notation so' `∘ₛ` so := oracle_compose so so'

variables (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'')

end compose

section oracle_append

def simulation_oracle_append (spec₁ spec₂ spec' : oracle_spec)
  (so : simulation_oracle spec₁ spec') (so' : simulation_oracle spec₂ spec') :
  simulation_oracle (spec₁ ++ spec₂) spec' :=
{ S := so.S × so'.S,
  o := λ i, match i with
  | sum.inl i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so.o i ⟨t, s.1⟩, return (u, s', s.2) }
  | sum.inr i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so'.o i ⟨t, s.2⟩, return (u, s.1, s') }
  end }

notation so `⟪++⟫` so' := simulation_oracle_append _ _ _ so so'

noncomputable example : simulation_oracle (coin_oracle ++ uniform_selecting) uniform_selecting :=
random_simulation_oracle coin_oracle ⟪++⟫ identity_oracle uniform_selecting

end oracle_append

section simulate_sides

def simulate_right {spec spec' : oracle_spec}
  (so : simulation_oracle spec' spec) :
  simulation_oracle (spec ++ spec') spec :=
identity_oracle spec ⟪++⟫ so

end simulate_sides
