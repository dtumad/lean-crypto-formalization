import computational_monads.simulation_semantics.default_simulate

/-!
# Tracking Simulation Oracle

This file defines a constructor for simulation oracles that use the internal state
for the purpose of tracking some value, in a way that doesn't affect the actual query result.
For example a logging oracle just tracks the queries, without actually affecting the return value.

The definition is in terms of a query function that responds to queries,
and an indepdent update_state function that controls the internal state.
For simplicity the update state function rather than having oracle access.

In many cases this definition will be composed with an oracle with result depending on the state,
but this construction allows seperation of the components that affect state independently.
-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Oracle where the query result is indepenent of the current oracle state,
although the new state may depend upon the previous state.
For example a logging oracle that just tracks the input and output of queries. -/
@[simps]
def tracking_oracle {spec : oracle_spec} {S : Type} (default_state : S)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S) :
  simulation_oracle spec spec' :=
{ S := S,
  default_state := default_state,
  o := λ i ⟨t, s⟩, do { u ← o i t, pure (u, update_state s i t u) } }

notation `⟪` o `|` update_state `,` default_state `⟫` :=
  tracking_oracle default_state o update_state

namespace tracking_oracle

variables {S : Type} (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state update_state' : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state default_state' : S) (a : α) (i : spec.ι) (t : spec.domain i)
  (x : spec.domain i × S) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s s' : S)

@[simp]
lemma apply_eq : ⟪o | update_state, default_state⟫.o i x =
  do { u ← o i x.1, pure (u, update_state x.2 i x.1 u) } := by {cases x, refl}

section support

@[simp]
lemma support_apply : ((⟪o | update_state, default_state⟫).o i (t, s)).support
  = { u | u.1 ∈ (o i t).support ∧ u.2 = update_state s i t u.1 } :=
set.ext (λ x, begin
  simp only [apply_eq, support_bind, support_pure, set.mem_Union,
    set.mem_singleton_iff, exists_prop, set.mem_set_of_eq, prod.eq_iff_fst_eq_snd_eq],
  refine ⟨λ h, let ⟨x₁, h, h'⟩ := h in h'.1.symm ▸ ⟨h, h'.2⟩, λ h, ⟨x.1, ⟨h.1, rfl, h.2⟩⟩⟩,
end)

/-- The support of `simulate'` is independing of the tracking oracle 
  TODO: I think this makes more sense using `stateless_oracle` stuff?-/
lemma support_simulate'_eq_of_oracle_eq :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support
    = (simulate' ⟪o | update_state', default_state'⟫ oa s').support :=
begin
  induction oa using oracle_comp.induction_on with a A A B oa ob hoa hob i t generalizing s,
  { simp },
  {

    ext x,
    simp only [support_simulate'_bind],
    simp [support_simulate'_bind, hoa, hob],
    refine ⟨λ h, _, λ h, _⟩,
    {
      obtain ⟨a, ⟨s, h⟩, ⟨s', h'⟩⟩ := h,
      refine ⟨a, _⟩,
      sorry
    },
    {
      sorry, 
    }
  },
  sorry,
end

lemma support_default_simulate'_eq_of_oracle_eq (oa : oracle_comp spec α) :
  (default_simulate' ⟪o | update_state, default_state⟫ oa).support =
    (default_simulate' ⟪o | update_state', default_state'⟫ oa).support :=
support_simulate'_eq_of_oracle_eq o update_state update_state' default_state default_state' oa _ _

lemma support_simulate'

end support

section distribution_semantics

open distribution_semantics

variable [spec.finite_range]

section equiv



-- TODO: should be able to find some generalization for lemmas looking like this
lemma simulate'_query_equiv_self (oa : oracle_comp spec α) (s : S) :
  simulate' (⟪query | update_state, default_state⟫) oa s ≃ₚ oa :=
begin
  sorry,
  -- induction oa with A a A B oa ob hoa hob i t generalizing s,
  -- { simp only [pure'_eq_pure, simulate'_pure, map_pure_equiv, eval_dist_return] },
  -- { let so := ⟪query | update_state, default_state⟫,
  --   calc simulate' so (oa >>= ob) s
  --     ≃ₚ simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 : simulate'_bind_equiv _ oa ob _
  --     ... ≃ₚ simulate so oa s >>= λ x, (ob x.1) : bind_equiv_of_equiv_second _ (by simp [hob])
  --     ... ≃ₚ simulate' so oa s >>= ob : symm (bind_map_equiv _ prod.fst ob)
  --     ... ≃ₚ oa >>= ob : bind_equiv_of_equiv_first ob (hoa _) },
  -- { erw [simulate'_query_equiv, tracking_oracle_o,
  --     fst_map_bind_mk_equiv, map_id_equiv (query i t)], } 
end

end equiv

section prob_event

end prob_event

end distribution_semantics

end tracking_oracle