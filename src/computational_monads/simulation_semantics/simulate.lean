import computational_monads.oracle_comp
import computational_monads.distribution_semantics.eval_distribution

namespace oracle_comp

variables {A B : Type} {spec spec' : oracle_spec}

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle
  
  `default_state` can be provided as a standard initial state for simulation.
  Used when calling `default_simulate` or `default_simulate'` -/
structure simulation_oracle (spec spec' : oracle_spec) :=
(S : Type)
(default_state : S)
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

section pure

variables (a : A) (s : so.S)

@[simp]
lemma simulate_pure : simulate so (pure a) s = pure (a, s) := rfl

lemma simulate_pure' : simulate so (pure' A a) s = pure (a, s) := rfl

lemma simulate_return : simulate so (return a) s = pure (a, s) := rfl

@[simp]
lemma eval_distribution_simulate_pure [spec'.finite_range] :
  ⟦simulate so (pure a) s⟧ = pmf.pure (a, s) := rfl

end pure

section bind

variables (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (s : so.S)

@[simp]
lemma simulate_bind : simulate so (oa >>= ob) s =
  (simulate so oa s) >>= (λ x, simulate so (ob x.1) x.2) := rfl

lemma simulate_bind' : simulate so (bind' A B oa ob) s =
  (simulate so oa s) >>= (λ x, simulate so (ob x.1) x.2) := rfl

@[simp]
lemma eval_distribution_simulate_bind [spec'.finite_range] :
  ⟦simulate so (oa >>= ob) s⟧ = ⟦simulate so oa s⟧ >>= (λ x, ⟦simulate so (ob x.1) x.2⟧) :=
by rw [simulate_bind, eval_distribution_bind]

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (s : so.S)

@[simp]
lemma simulate_query : simulate so (query i t) s = so.o i (t, s) := rfl

@[simp]
lemma eval_distribution_simulate_query [spec'.finite_range] :
  ⟦simulate so (query i t) s⟧ = ⟦so.o i (t, s)⟧ := rfl

end query

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

section default_simulate

/-- TODO: expand this and use everywhere -/
@[reducible, inline]
def default_simulate (so : simulation_oracle spec spec') (oa : oracle_comp spec A) :
  oracle_comp spec' (A × so.S) :=
oa.simulate so so.default_state

end default_simulate

section default_simulate'

@[reducible, inline]
def default_simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec A) :
  oracle_comp spec' A :=
oa.simulate' so so.default_state

end default_simulate'

end oracle_comp