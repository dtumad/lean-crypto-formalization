import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.stateless_oracle

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec}

section compose

def oracle_compose {spec spec' spec'' : oracle_spec}
  (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'') :
  simulation_oracle spec spec'' :=
{ S := so.S × so'.S,
  o := λ i ⟨t, s, s'⟩, simulate so' (so.o i (t, s)) s' >>= λ ⟨⟨u, s⟩, s'⟩, return (u, s, s') }

notation so' `∘ₛ` so := oracle_compose so so'

variables (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'')


end compose

section query_log

def query_log (spec : oracle_spec) : Type :=
list (Σ (i : spec.ι), spec.domain i × spec.range i)

/-- Looking up a cache value requires use of the first equality condition
  to make the following conditions and return values type correct. -/
def query_log.lookup {spec : oracle_spec} [spec.computable] :
  Π (log : query_log spec) (i : spec.ι) (t : spec.domain i), option (spec.range i)
| (⟨i', t', u⟩ :: log) i t := if hi : i' = i
    then (if t = hi.rec_on t' then hi.rec_on (some u)
    else query_log.lookup log i t) else query_log.lookup log i t
| [] i t := none

end query_log

section logging_oracle

/-- Extend the state of a simulation oracle to also track the inputs and outputs of queries.
  The actual oracle calls are forwarded directly to the original oracle. -/
def logging_simulation_oracle (spec spec' : oracle_spec)
  (so : simulation_oracle spec spec') : simulation_oracle spec spec' :=
{ S := so.S × query_log spec,
  o := λ i ⟨t, ⟨s, log⟩⟩, so.o i (t, s) >>= λ ⟨u, s⟩, return (u, (s, ⟨i, t, u⟩ :: log)) }

end logging_oracle

section caching_oracle

-- TODO: make this a extension property instead.
def caching_simulation_oracle (spec : oracle_spec) [spec.computable] :
  simulation_oracle spec spec :=
{ S := query_log spec,
  o := λ i ⟨t, log⟩, match query_log.lookup i t log with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do { u ← query i t, return (u, ⟨i, t, u⟩ :: log) }
  end }

end caching_oracle

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
