import computational_monads.oracle_comp
import computational_monads.distribution_semantics.prob_event
import computational_monads.distribution_semantics.equiv

namespace oracle_comp

variables {A B C : Type} {spec spec' spec'' : oracle_spec}

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle
  
  `default_state` can be provided as a standard initial state for simulation.
  Used when calling `default_simulate` or `default_simulate'` -/
structure simulation_oracle (spec spec' : oracle_spec) :=
(S : Type)
(default_state : S)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

variables (so : simulation_oracle spec spec') (so' : simulation_oracle spec spec'')
variables (a : A) (i : spec.ι) (t : spec.domain i)
  (oa oa' : oracle_comp spec A) (ob ob' : A → oracle_comp spec B) (s : so.S)

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

lemma support_simulate_pure : (simulate so (pure a) s).support = {(a, s)} :=
by simp

lemma support_simulate_bind : (simulate so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support :=
by simp

lemma support_simulate_query : (simulate so (query i t) s).support = (so.o i (t, s)).support :=
by simp

section eval_distribution

open distribution_semantics

variable [spec'.finite_range]

lemma eval_distribution_simulate_pure :
  ⦃simulate so (pure a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_distribution_simulate_bind :
  ⦃simulate so (oa >>= ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
by rw [simulate_bind, eval_distribution_bind]

lemma eval_distribution_simulate_query :
  ⦃simulate so (query i t) s⦄ = ⦃so.o i (t, s)⦄ := rfl

@[simp]
lemma simulate_pure_equiv : (simulate so (pure a) s) ≃ₚ
  (pure (a, s) : oracle_comp spec' (A × so.S)) := rfl

@[simp]
lemma simulate_bind_equiv : (simulate so (oa >>= ob) s) ≃ₚ
  (simulate so oa s) >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp]
lemma simulate_query_equiv : (simulate so (query i t) s) ≃ₚ so.o i (t, s) := rfl

end eval_distribution

end simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
def simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec A) (s : so.S) :
  oracle_comp spec' A := prod.fst <$> oa.simulate so s

@[simp]
lemma simulate'_pure : simulate' so (pure a) s = prod.fst <$> (pure (a, s)) := rfl

@[simp]
lemma simulate'_bind : simulate' so (oa >>= ob) s =
  (simulate so oa s >>= λ x, simulate' so (ob x.1) x.2) :=
sorry

@[simp]
lemma simulate'_query : simulate' so (query i t) s = prod.fst <$> so.o i (t, s) := rfl

@[simp]
lemma support_simulate' : (simulate' so oa s).support =
  prod.fst '' (simulate so oa s).support :=
by simp [simulate']

lemma support_simulate'_pure (a : A) : (simulate' so (pure a) s).support = {a} :=
by simp

lemma support_simulate'_bind : (simulate' so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
by simp

lemma support_simulate'_query : (simulate' so (query i t) s).support =
  prod.fst '' (so.o i (t, s)).support :=
by simp

section eval_distribution

open distribution_semantics

variable [spec'.finite_range]

lemma eval_distribution_simulate' : ⦃simulate' so oa s⦄ = prod.fst <$> ⦃simulate so oa s⦄ :=
eval_distribution_map _ prod.fst

lemma eval_distribution_simulate'_pure : ⦃simulate' so (pure a) s⦄ = pmf.pure a :=
by simp [pmf.pure_map]

lemma eval_distribution_simulate'_bind :
  ⦃simulate' so (oa >>= ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate' so (ob x.1) x.2⦄ :=
by simp [simulate']

lemma eval_distribution_simulate'_query :
  ⦃simulate' so (query i t) s⦄ = prod.fst <$> ⦃so.o i (t, s)⦄ :=
by {simp, refl}

lemma simulate'_equiv_fst_map_simulate :
  simulate' so oa s ≃ₚ prod.fst <$> simulate so oa s := rfl

@[simp]
lemma simulate'_pure_equiv : simulate' so (pure a) s ≃ₚ
  (pure a : oracle_comp spec' A) := by simp only [simulate'_pure, map_pure_equiv]

@[simp]
lemma simulate'_bind_equiv : simulate' so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 :=
by simp [simulate']

@[simp]
lemma simulate'_query_equiv : simulate' so (query i t) s ≃ₚ
  prod.fst <$> (so.o i (t, s)) := rfl

end eval_distribution

end simulate'

end oracle_comp