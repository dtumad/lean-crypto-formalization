import computational_monads.simulation_semantics.simulate

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
For example a logging oracle that just tracks the input and output of queries.
`o` is the way the oracle responds to queries, which doesn't have access to the state.
`update_state` takes a query and internal state and returns the new internal state.
Note that `update_state` is not a probabalistic function, and has no oracle access -/
def tracking_oracle {spec : oracle_spec} {S : Type}
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state : S) : sim_oracle spec spec' S :=
{ default_state := default_state,
  o := λ i ⟨t, s⟩, (λ u, (u, update_state s i t u)) <$> (o i t) }

notation `⟪` o `|` update_state `,` default_state `⟫` :=
  tracking_oracle o update_state default_state

namespace tracking_oracle

variables {S S' : Type} (o o' : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (update_state' : Π (s : S') (i : spec.ι), spec.domain i → spec.range i → S')
  (default_state : S) (default_state' : S') (a : α) (i : spec.ι) (t : spec.domain i)
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s : S) (s' : S')
  (x : spec.domain i × S) (y : spec.range i × S)

@[simp]
lemma apply_eq : ⟪o | update_state, default_state⟫ i x =
  (λ u, (u, update_state x.2 i x.1 u)) <$> (o i x.1) := by {cases x, refl}

section support

@[simp]
lemma support_apply : (⟪o | update_state, default_state⟫ i x).support =
  {y | y.1 ∈ (o i x.1).support ∧ y.2 = update_state x.2 i x.1 y.1} :=
set.ext (λ y, by {
  simp only [prod.eq_iff_fst_eq_snd_eq, apply_eq, support_map,
    set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_set_of_eq],
  exact ⟨λ h, let ⟨u, h, h'⟩ := h in h' ▸ ⟨h, rfl⟩,
    λ h, ⟨y.1, h.1, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, h.2.symm⟩⟩⟩ } )

/-- If the oracle can take on any value then the first element of the support is unchanged -/
theorem support_simulate'_eq_support (h : ∀ i t, (o i t).support = ⊤) :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support = oa.support :=
begin
  refine support_simulate'_eq_support _ oa s (λ i t s, _),
  simp only [set.top_eq_univ, set.eq_univ_iff_forall, h, support_apply, set.mem_univ, forall_const,
    true_and, set.mem_image, set.mem_set_of_eq, prod.exists, exists_eq_left, exists_apply_eq_apply]
end

/-- Particular case of `support_simulate'_eq_support` for `query` -/
lemma support_simulate'_query_oracle_eq_support :
  (simulate' ⟪query | update_state, default_state⟫ oa s).support = oa.support :=
support_simulate'_eq_support query update_state default_state oa s (λ _ _, rfl)

/-- The support of `simulate'` is independing of the tracking oracle -/
lemma support_simulate'_eq_of_oracle_eq :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support =
    (simulate' ⟪o | update_state', default_state'⟫ oa s').support :=
begin
  refine support_simulate'_eq_support_simulate' (λ i t t t', set.ext $ λ x, _) oa s s',
  simp only [simulate'_query, support_map, support_apply, set.mem_image, set.mem_set_of_eq,
    prod.exists, exists_and_distrib_right, exists_eq_right],
end

end support

section distribution_semantics

open distribution_semantics

section eval_dist

@[simp]
lemma eval_dist_apply [spec'.finite_range] :
  ⦃⟪o | update_state, default_state⟫ i (t, s)⦄ = ⦃o i t⦄.map (λ u, (u, update_state s i t u)) :=
by rw [apply_eq, eval_dist_map]

lemma eval_dist_simulate'_eq_eval_dist [spec.finite_range] [spec'.finite_range] :
  ⦃simulate' ⟪o | update_state, default_state⟫ oa s⦄ = ⦃oa⦄ :=
begin
  refine pmf.ext (λ a, _),
  refine eval_dist_simulate'_apply_eq_induction _ oa s a _ _,
end



end eval_dist

section equiv



-- -- TODO: should be able to find some generalization for lemmas looking like this
-- lemma simulate'_query_equiv_self [spec.finite_range] :
--   simulate' (⟪query | update_state, default_state⟫) oa s ≃ₚ oa :=
-- begin
--   sorry,
--   -- { simp only [pure'_eq_pure, simulate'_pure, map_pure_equiv, eval_dist_return] },
--   -- { let so := ⟪query | update_state, default_state⟫,
--   --   calc simulate' so (oa >>= ob) s
--   --     ≃ₚ simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 : simulate'_bind_equiv _ oa ob _
--   --     ... ≃ₚ simulate so oa s >>= λ x, (ob x.1) : bind_equiv_of_equiv_second _ (by simp [hob])
--   --     ... ≃ₚ simulate' so oa s >>= ob : symm (bind_map_equiv _ prod.fst ob)
--   --     ... ≃ₚ oa >>= ob : bind_equiv_of_equiv_first ob (hoa _) },
--   -- { erw [simulate'_query_equiv, tracking_oracle_o,
--   --     fst_map_bind_mk_equiv, map_id_equiv (query i t)], } 
-- end

end equiv

section prob_event

end prob_event

end distribution_semantics

end tracking_oracle