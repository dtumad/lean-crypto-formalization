import computational_monads.oracle_comp
import computational_monads.distribution_semantics.prob_event

namespace oracle_comp

variables {A B C : Type} {spec spec' : oracle_spec}

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
  (simulate so oa so.default_state).support := rfl

end default_simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
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
by simp [simulate']

end simulate'

section default_simulate'

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
  (simulate' so oa so.default_state).support := rfl

end default_simulate'

section eval_distribution

variable [hspec' : spec'.finite_range]
include hspec'

section simulate

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

end simulate

section default_simulate

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

end default_simulate

section simulate'

lemma eval_distribution_simulate' :
  ⟦simulate' so oa s⟧ = prod.fst <$> ⟦simulate so oa s⟧ :=
eval_distribution_map _ prod.fst

@[simp]
lemma eval_distribution_simulate'_pure : 
  ⟦simulate' so (pure a) s⟧ = pmf.pure a :=
by simp [pmf.pure_map]

@[simp]
lemma eval_distribution_simulate'_bind :
  ⟦simulate' so (oa >>= ob) s⟧ = ⟦simulate so oa s⟧ >>= λ x, ⟦simulate' so (ob x.1) x.2⟧ :=
begin
  simp [simulate'_def], refine pmf.bind_map ⟦simulate so oa s⟧ _ prod.fst,
end

@[simp]
lemma eval_distribution_simulate'_query :
  ⟦simulate' so (query i t) s⟧ = prod.fst <$> ⟦so.o i (t, s)⟧ :=
begin
  simp, refl,
end

-- TODO: clean this up a bunch
/-- If the state of the oracle is independent of the query output,
  then dropping the state at the end is equivalent to the original computation. -/
lemma eval_distribution_simulate'_of_indep_state [spec.finite_range]
  (state_f : so.S → Π (i : spec.ι), spec.domain i → spec.range i → so.S)
  (h : ∀ (s : so.S) (i : spec.ι) (t : spec.domain i),
    ⟦so.o i (t, s)⟧ = ⟦query i t >>= λ u, return (u, state_f s i t u)⟧) :
  ⟦simulate' so oa s⟧ = ⟦oa⟧ :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  {
    simp [pmf.pure_map],
  },
  {
    rw [bind'_eq_bind],
    rw [eval_distribution_simulate'_bind],
    rw [eval_distribution_bind],
    simp at hob,
    simp [hob],
    refine trans (pmf.bind_ ⟦simulate so oa s⟧ (λ a, ⟦ob a⟧) prod.fst) _,
    congr,
    refine trans _ (hoa s),
    rw eval_distribution_simulate',
  },
  {
    -- TODO: this should be simpler after pmf lawful functor stuff
    rw [eval_distribution_simulate'_query],
    rw [h],
    rw [eval_distribution_bind],
    rw [pmf.bind_map],
    simp [pmf.bind_map, functor.map, pmf.bind_pure],
    refine pmf.bind_pure _,
  }
end

end simulate'

section default_simulate'

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

end default_simulate'

end eval_distribution

end oracle_comp