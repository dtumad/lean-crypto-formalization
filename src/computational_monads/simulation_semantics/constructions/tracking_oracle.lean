import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}
  (oa : oracle_comp spec A)

-- TODO: use namespaces to simplify the lemma names

-- TODO: should be able to use `simps` everywhere instead of implementing projections

/-- Oracle where the query result is indepenent of the current oracle state,
  although the new state may depend upon the previous state.
  For example a logging oracle that just tracks the input and output of queries. -/
@[simps]
def tracking_oracle {S : Type} (default_state : S)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S) :
  simulation_oracle spec spec' :=
{ S := S,
  default_state := default_state,
  o := λ i ⟨t, s⟩, do { u ← o i t, pure (u, update_state s i t u) } }

notation `⟪` o `|` update_state `,` default_state `⟫` :=
  tracking_oracle default_state o update_state

variables {S : Type} (default_state : S)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)

-- TODO: should be able to find some generalization for lemmas looking like this
lemma simulate'_tracking_oracle_query_equiv [spec.finite_range]
  (s : S) : simulate' (⟪query | update_state, default_state⟫) oa s ≃ₚ oa :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { simp only [pure'_eq_pure, simulate'_pure, pure_map_equiv, eval_distribution_return] },
  { let so := ⟪query | update_state, default_state⟫,
    calc simulate' so (oa >>= ob) s
      ≃ₚ simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 : simulate'_bind_equiv _ oa ob _
      ... ≃ₚ simulate so oa s >>= λ x, (ob x.1) : bind_equiv_of_equiv_second _ (by simp [hob])
      ... ≃ₚ simulate' so oa s >>= ob : symm (bind_map_equiv _ prod.fst ob)
      ... ≃ₚ oa >>= ob : bind_equiv_of_equiv_first ob (hoa _) },
  { erw [simulate'_query_equiv, tracking_oracle_o,
      fst_map_bind_mk_equiv, map_id_equiv (query i t)], } 
end