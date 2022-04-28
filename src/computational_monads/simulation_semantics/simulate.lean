import computational_monads.oracle_comp

namespace oracle_comp

variables {A B : Type} {spec spec' : oracle_spec}

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle -/
structure simulation_oracle (spec spec' : oracle_spec) :=
(S : Type)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

section simulate

/-- Simulate an oracle comp to an oracle comp with a different spec.
  Requires providing a maximum recursion depth for the `repeat` constructor -/
def simulate {spec spec' : oracle_spec} (so : simulation_oracle spec spec') :
  Π {A : Type} (oa : oracle_comp spec A), so.S → oracle_comp spec' (A × so.S)
| _ (pure' A a) state := return ⟨a, state⟩
| _ (bind' A B oa ob) state := simulate oa state >>= λ x, simulate (ob x.1) x.2
| _ (query i t) state := so.o i (t, state)

/-- Get the result of simulation without returning the internal oracle state -/
@[reducible, inline]
def simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec A) (s : so.S) :
  oracle_comp spec' A :=
prod.fst <$> oa.simulate so s

def sim_comp {spec spec' spec'' : oracle_spec}
  (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'') :
  simulation_oracle spec spec'' :=
{ S := so.S × so'.S,
  o := λ i ⟨x, s⟩, begin
    sorry
  end
}

variables (so : simulation_oracle spec spec')

@[simp]
lemma simulate_pure (a : A) (s : so.S) :
  simulate so (pure a) s = pure (a, s) := rfl

lemma simulate_pure' (a : A) (s : so.S) :
  simulate so (pure' A a) s = pure' (A × so.S) (a, s) := rfl

lemma simulate_return (a : A) (s : so.S) :
  simulate so (return a) s = return (a, s) := rfl

@[simp]
lemma simulate_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (s : so.S) :
  simulate so (oa >>= ob) s = (simulate so oa s) >>= (λ x, simulate so (ob x.1) x.2) := rfl

lemma simulate_bind' (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (s : so.S) :
  simulate so (bind' A B oa ob) s = bind (simulate so oa s) (λ x, simulate so (ob x.1) x.2) := rfl

@[simp]
lemma simulate_query  (i : spec.ι) (t : spec.domain i) (s : so.S) :
  simulate so (query i t) s = so.o i (t, s) := rfl

end simulate

end oracle_comp