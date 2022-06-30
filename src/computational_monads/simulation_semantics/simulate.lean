import computational_monads.oracle_comp
import computational_monads.distribution_semantics.prob_event

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
variables (a : A) (i : spec.ι) (t : spec.domain i)
  (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (s : so.S)

section simulate

/-- Simulate an oracle comp to an oracle comp with a different spec.
  Requires providing a maximum recursion depth for the `repeat` constructor -/
def simulate {spec spec' : oracle_spec} (so : simulation_oracle spec spec') :
  Π {A : Type} (oa : oracle_comp spec A), so.S → oracle_comp spec' (A × so.S)
| _ (pure' A a) state := return ⟨a, state⟩
| _ (bind' A B oa ob) state := simulate oa state >>= λ x, simulate (ob x.1) x.2
| _ (query i t) state := so.o i (t, state)

@[simp]
lemma simulate_pure : simulate so (pure a) s = pure (a, s) := rfl

@[simp]
lemma simulate_bind : simulate so (oa >>= ob) s =
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp]
lemma simulate_query : simulate so (query i t) s = so.o i (t, s) := rfl

lemma support_simulate_pure :
  (simulate so (pure a) s).support = {(a, s)} :=
by simp

lemma support_simulate_bind : (simulate so (oa >>= ob) s).support =
  ⋃ (x : A × so.S) (hx : x ∈ (simulate so oa s).support), (simulate so (ob x.1) x.2).support :=
by simp

lemma support_simulate_query : (simulate so (query i t) s).support = (so.o i (t, s)).support :=
by simp

end simulate

section default_simulate

/-- TODO: expand this and use everywhere -/
@[reducible, inline]
def default_simulate (so : simulation_oracle spec spec') (oa : oracle_comp spec A) :
  oracle_comp spec' (A × so.S) := oa.simulate so so.default_state

lemma default_simulate_def : oa.default_simulate so = oa.simulate so so.default_state := rfl 

@[simp]
lemma default_simulate_pure : default_simulate so (pure a) = pure (a, so.default_state) := rfl

@[simp]
lemma default_simulate_bind : default_simulate so (oa >>= ob) =
  simulate so oa so.default_state >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp]
lemma default_simulate_query : default_simulate so (query i t) =
  so.o i (t, so.default_state) := rfl

lemma support_default_simulate : (default_simulate so oa).support =
  (simulate so oa so.default_state).support :=
by simp

end default_simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
@[reducible, inline]
def simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec A) (s : so.S) :
  oracle_comp spec' A := prod.fst <$> oa.simulate so s

lemma simulate'_def : oa.simulate' so s = prod.fst <$> oa.simulate so s := rfl

@[simp]
lemma simulate'_pure : simulate' so (pure a) s = prod.fst <$> (pure (a, s)) := rfl

@[simp]
lemma simulate'_bind : simulate' so (oa >>= ob) s =
  prod.fst <$> (simulate so oa s >>= λ x, simulate so (ob x.1) x.2) := rfl

@[simp]
lemma simulate'_query : simulate' so (query i t) s = prod.fst <$> so.o i (t, s) := rfl

lemma support_simulate' : (simulate' so oa s).support =
  prod.fst '' (simulate so oa s).support :=
by simp

end simulate'

section default_simulate'

@[reducible, inline]
def default_simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec A) :
  oracle_comp spec' A := oa.simulate' so so.default_state

lemma default_simulate'_def : oa.default_simulate' so = oa.simulate' so so.default_state := rfl

@[simp]
lemma default_simulate'_pure : default_simulate' so (pure a) =
  prod.fst <$> pure (a, so.default_state) := rfl

@[simp]
lemma default_simulate'_bind : default_simulate' so (oa >>= ob) =
  prod.fst <$> ((simulate so oa so.default_state) >>= (λ x, simulate so (ob x.1) x.2)) := rfl

@[simp]
lemma default_simulate'_query : default_simulate' so (query i t) =
  prod.fst <$>so.o i (t, so.default_state) := rfl

lemma support_default_simulate' : (default_simulate' so oa).support =
  (simulate' so oa so.default_state).support :=
by simp

end default_simulate'

section eval_distribution

variable [hspec' : spec'.finite_range]
include hspec'

@[simp]
lemma eval_distribution_simulate_pure :
  ⟦simulate so (pure a) s⟧ = pmf.pure (a, s) := rfl

@[simp]
lemma eval_distribution_simulate_bind :
  ⟦simulate so (oa >>= ob) s⟧ = ⟦simulate so oa s⟧ >>= λ x, ⟦simulate so (ob x.1) x.2⟧ :=
by rw [simulate_bind, eval_distribution_bind]

@[simp]
lemma eval_distribution_simulate_query :
  ⟦simulate so (query i t) s⟧ = ⟦so.o i (t, s)⟧ := rfl

@[simp]
lemma eval_distribution_default_simulate_pure :
  ⟦default_simulate so (pure a)⟧ = pmf.pure (a, so.default_state) :=
eval_distribution_simulate_pure so a so.default_state

@[simp]
lemma eval_distribution_default_simulate_bind :
  ⟦default_simulate so (oa >>= ob)⟧ =
    ⟦simulate so oa so.default_state⟧ >>= λ x, ⟦simulate so (ob x.1) x.2⟧ :=
eval_distribution_simulate_bind so oa ob so.default_state

@[simp]
lemma eval_distribution_default_simulate_query :
  ⟦default_simulate so (query i t)⟧ = ⟦so.o i (t, so.default_state)⟧ :=
eval_distribution_simulate_query so i t so.default_state

@[simp]
lemma eval_distribution_simulate'_pure : 
  ⟦simulate' so (pure a) s⟧ = pmf.pure a :=
by simp [pmf.pure_map]

@[simp]
lemma eval_distribution_simulate'_bind :
  ⟦simulate' so (oa >>= ob) s⟧ = ⟦simulate so oa s⟧ >>= λ x, ⟦simulate' so (ob x.1) x.2⟧ :=
begin
  simp, refine pmf.bind_map ⟦simulate so oa s⟧ _ prod.fst,
end

@[simp]
lemma eval_distribution_simulate'_query :
  ⟦simulate' so (query i t) s⟧ = prod.fst <$> ⟦so.o i (t, s)⟧ :=
begin
  simp, refl,
end

@[simp]
lemma eval_distribution_default_simulate'_pure :
  ⟦default_simulate' so (pure a)⟧ = pmf.pure a :=
eval_distribution_simulate'_pure so a so.default_state

@[simp]
lemma eval_distribution_default_simulate'_bind :
  ⟦default_simulate' so (oa >>= ob)⟧ =
    ⟦default_simulate so oa⟧ >>= λ x, ⟦simulate' so (ob x.1) x.2⟧ :=
eval_distribution_simulate'_bind so oa ob so.default_state

@[simp]
lemma eval_distribution_default_simulate'_query :
  ⟦default_simulate' so (query i t)⟧ = prod.fst <$> ⟦simulate so (query i t) so.default_state⟧ :=
eval_distribution_simulate'_query so i t so.default_state

end eval_distribution

end oracle_comp