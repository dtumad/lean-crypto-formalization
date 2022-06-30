import computational_monads.oracle_comp
import computational_monads.distribution_semantics.eval_distribution

namespace oracle_comp

variables {A B : Type} {spec spec' : oracle_spec}

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle
  TODO: `default_state` to avoid constantly providing oracles -/
structure simulation_oracle (spec spec' : oracle_spec) :=
(S : Type)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

variables (so : simulation_oracle spec spec')

section simulate

/-- Simulate an oracle comp to an oracle comp with a different spec.
  Requires providing a maximum recursion depth for the `repeat` constructor -/
def simulate {spec spec' : oracle_spec} (so : simulation_oracle spec spec') :
  Π {A : Type} (oa : oracle_comp spec A), so.S → oracle_comp spec' (A × so.S)
| _ (pure' A a) state := return ⟨a, state⟩
| _ (bind' A B oa ob) state := simulate oa state >>= λ x, simulate (ob x.1) x.2
| _ (query i t) state := so.o i (t, state)

@[simp]
lemma simulate_pure (a : A) (s : so.S) :
  simulate so (pure a) s = pure (a, s) := rfl

lemma eval_distribution_simulate_pure [spec'.finite_range] (a : A) (s : so.S) :
  ⟦simulate so (pure a) s⟧ = pmf.pure (a, s) := rfl

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
lemma simulate_query (i : spec.ι) (t : spec.domain i) (s : so.S) :
  simulate so (query i t) s = so.o i (t, s) := rfl

end simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
@[reducible, inline]
def simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec A) (s : so.S) :
  oracle_comp spec' A :=
prod.fst <$> oa.simulate so s

@[simp]
lemma simulate'_pure (a : A) (s : so.S) :
  simulate' so (pure a) s = prod.fst <$> (pure (a, s)) := rfl

@[simp]
lemma simulate'_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (s : so.S) :
  simulate' so (oa >>= ob) s =
    prod.fst <$> ((simulate so oa s) >>= (λ x, simulate so (ob x.1) x.2)) := rfl

@[simp]
lemma simulate'_query (i : spec.ι) (t : spec.domain i) (s : so.S) :
  simulate' so (query i t) s = prod.fst <$> so.o i (t, s) := rfl

@[simp]
lemma eval_distribution_simulate'_pure [spec'.finite_range] (a : A) (s : so.S) :
  ⟦(simulate' so (pure a) s)⟧ = pmf.pure a :=
by simp only [pmf.pure_map, simulate'_pure, eval_distribution_map, eval_distribution_return]

end simulate'

end oracle_comp