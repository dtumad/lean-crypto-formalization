import computational_monads.simulation_semantics.simulate

namespace oracle_comp

variables {A B C : Type} {spec spec' spec'' : oracle_spec}
  (so : simulation_oracle spec spec') (so' : simulation_oracle spec spec'')
  (a : A) (i : spec.ι) (t : spec.domain i)
  (oa oa' : oracle_comp spec A) (ob ob' : A → oracle_comp spec B) (s : so.S)

section default_simulate

/-- TODO: expand this and use everywhere -/
def default_simulate (so : simulation_oracle spec spec') (oa : oracle_comp spec A) :
  oracle_comp spec' (A × so.S) := oa.simulate so so.default_state

@[simp]
lemma default_simulate_pure : default_simulate so (pure a) = pure (a, so.default_state) := rfl

@[simp]
lemma default_simulate_bind : default_simulate so (oa >>= ob) =
  simulate so oa so.default_state >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp]
lemma default_simulate_query : default_simulate so (query i t) =
  so.o i (t, so.default_state) := rfl

@[simp]
lemma support_default_simulate : (default_simulate so oa).support =
  (simulate so oa so.default_state).support := rfl

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

lemma eval_distribution_default_simulate_pure :
  ⦃default_simulate so (pure a)⦄ = pmf.pure (a, so.default_state) :=
eval_distribution_simulate_pure so a so.default_state

lemma eval_distribution_default_simulate_bind :
  ⦃default_simulate so (oa >>= ob)⦄ =
    ⦃simulate so oa so.default_state⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
eval_distribution_simulate_bind so oa ob so.default_state

lemma eval_distribution_default_simulate_query :
  ⦃default_simulate so (query i t)⦄ = ⦃so.o i (t, so.default_state)⦄ :=
eval_distribution_simulate_query so i t so.default_state

@[simp]
lemma default_simulate_pure_equiv : default_simulate so (pure a) ≃ₚ
  (pure (a, so.default_state) : oracle_comp spec' (A × so.S)) := rfl

@[simp]
lemma default_simulate_bind_equiv : default_simulate so (oa >>= ob) ≃ₚ
  default_simulate so oa >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp]
lemma default_simulate_query_equiv : default_simulate so (query i t) ≃ₚ
  so.o i (t, so.default_state) := rfl

end distribution_semantics

end default_simulate

section default_simulate'

def default_simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec A) :
  oracle_comp spec' A := oa.simulate' so so.default_state

@[simp]
lemma default_simulate'_pure : default_simulate' so (pure a) =
  prod.fst <$> pure (a, so.default_state) := rfl

@[simp]
lemma default_simulate'_bind : default_simulate' so (oa >>= ob) =
  prod.fst <$> ((default_simulate so oa) >>= (λ x, simulate so (ob x.1) x.2)) := rfl

@[simp]
lemma default_simulate'_query : default_simulate' so (query i t) =
  prod.fst <$>so.o i (t, so.default_state) := rfl

@[simp]
lemma support_default_simulate' : (default_simulate' so oa).support =
  (simulate' so oa so.default_state).support := rfl

lemma support_default_simulate'_bind : (default_simulate' so (oa >>= ob)).support =
  ⋃ a ∈ (default_simulate so oa).support, (simulate' so (ob $ prod.fst a) a.2).support :=
by simp [set.image_Union]

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

lemma eval_distribution_default_simulate'_pure : ⦃default_simulate' so (pure a)⦄ =
  pmf.pure a := eval_distribution_simulate'_pure so a so.default_state

lemma eval_distribution_default_simulate'_bind : ⦃default_simulate' so (oa >>= ob)⦄ =
  ⦃default_simulate so oa⦄ >>= λ x, ⦃simulate' so (ob x.1) x.2⦄ :=
eval_distribution_simulate'_bind so oa ob so.default_state

lemma eval_distribution_default_simulate'_query : ⦃default_simulate' so (query i t)⦄ =
  prod.fst <$> ⦃simulate so (query i t) so.default_state⦄ :=
eval_distribution_simulate'_query so i t so.default_state

@[simp]
lemma default_simulate'_pure_equiv : default_simulate' so (pure a) ≃ₚ
  (pure a : oracle_comp spec' A) :=
simulate'_pure_equiv so a so.default_state

@[simp]
lemma default_simulate'_bind_equiv : default_simulate' so (oa >>= ob) ≃ₚ
  (default_simulate so oa) >>= λ x, simulate' so (ob x.1) x.2 :=
simulate'_bind_equiv so oa ob so.default_state

@[simp]
lemma default_simulate'_query_equiv : default_simulate' so (query i t) ≃ₚ
  prod.fst <$> (so.o i (t, so.default_state)) :=
simulate'_query_equiv so i t so.default_state

end distribution_semantics

end default_simulate'

end oracle_comp
