/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.support
import computational_monads.simulation_semantics.simulate.eval_dist

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

@[simp] lemma apply_eq : ⟪o | update_state, default_state⟫ i x =
  (λ u, (u, update_state x.2 i x.1 u)) <$> (o i x.1) := by {cases x, refl}

instance decidable [computable spec] [decidable_eq S] [∀ i x, (o i x).decidable] :
  (⟪o | update_state, default_state⟫ i x).decidable :=
by { rw [apply_eq], exact oracle_comp.decidable_map _ _ }

section support

@[simp] lemma support_apply : (⟪o | update_state, default_state⟫ i x).support =
  {y | y.1 ∈ (o i x.1).support ∧ y.2 = update_state x.2 i x.1 y.1} :=
set.ext (λ y, begin
  rw [apply_eq],
  -- simp only [prod.eq_iff_fst_eq_snd_eq, apply_eq, support_map,
  --   set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_set_of_eq],
  -- exact ⟨λ h, let ⟨u, h, h'⟩ := h in h' ▸ ⟨h, rfl⟩,
  --   λ h, ⟨y.1, h.1, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, h.2.symm⟩⟩⟩
end)

@[simp] lemma support_apply_of_subsingleton [subsingleton S] :
  (⟪o | update_state, default_state⟫ i x).support = prod.fst ⁻¹' (o i x.1).support :=
begin

end

/-- If the oracle can take on any value then the first element of the support is unchanged -/
theorem support_simulate'_eq_support (h : ∀ i t, (o i t).support = ⊤) :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support = oa.support :=
begin
  refine support_simulate'_eq_support _ oa s (λ i t s, _),
  simp only [set.top_eq_univ, set.eq_univ_iff_forall, h, support_apply, set.mem_univ, forall_const,
    true_and, set.mem_image, set.mem_set_of_eq, prod.exists, exists_eq_left, exists_apply_eq_apply]
end

/-- Particular case of `support_simulate'_eq_support` for `query`.
In particular a tracking oracle that *only* does tracking doesn't affect the main output. -/
lemma support_simulate'_query_oracle_eq_support :
  (simulate' ⟪query | update_state, default_state⟫ oa s).support = oa.support :=
support_simulate'_eq_support query update_state default_state oa s (λ _ _, rfl)

/-- The support of `simulate'` is independt of the tracking functions -/
theorem support_simulate'_eq_of_oracle_eq :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support =
    (simulate' ⟪o | update_state', default_state'⟫ oa s').support :=
begin
  refine support_simulate'_eq_support_simulate' (λ i t t t', set.ext $ λ x, _) oa s s',
  simp only [simulate'_query, support_map, support_apply, set.mem_image, set.mem_set_of_eq,
    prod.exists, exists_and_distrib_right, exists_eq_right],
end

end support

section fin_support


end fin_support

section distribution_semantics

open distribution_semantics

section eval_dist

@[simp] lemma eval_dist_apply [spec'.finite_range] :
  ⦃⟪o | update_state, default_state⟫ i (t, s)⦄ = ⦃o i t⦄.map (λ u, (u, update_state s i t u)) :=
by rw [apply_eq, eval_dist_map]

/-- If the oracle has uniform distribution, then the distribution under `simulate'` is unchanged -/
theorem eval_dist_simulate'_eq_eval_dist [spec.finite_range] [spec'.finite_range]
  (h : ∀ i t, ⦃o i t⦄ = pmf.uniform_of_fintype (spec.range i)) :
  ⦃simulate' ⟪o | update_state, default_state⟫ oa s⦄ = ⦃oa⦄ :=
eval_dist_simulate'_eq_eval_dist _ oa s (λ i t s, trans 
  (by simpa [eval_dist_apply, pmf.map_comp] using pmf.map_id ⦃o i t⦄) (h i t))

/-- Specific case of `eval_dist_simulate'_eq_eval_dist` for query.
In particular if a tracking oracle *only* does tracking gives the same main output distribution. -/
lemma eval_dist_simulate'_query_eq_eval_dist [spec.finite_range] :
  ⦃simulate' ⟪query | update_state, default_state⟫ oa s⦄ = ⦃oa⦄ :=
eval_dist_simulate'_eq_eval_dist query update_state default_state oa s (λ _ _, rfl)

/-- The first output of simulation under different `tracking_oracle` with the same oracle
is the same regardless of if the tracking functions are different. -/
theorem eval_dist_simulate'_eq_eval_dist_simulate' [spec'.finite_range] :
  ⦃simulate' ⟪o | update_state, default_state⟫ oa s⦄ =
    ⦃simulate' ⟪o | update_state', default_state'⟫ oa s'⦄ :=
eval_dist_simulate'_eq_eval_dist_simulate' (λ i t s s',
  by simp only [pmf.map_comp, apply_eq, eval_dist_map]) oa s s'

end eval_dist

section prob_event

@[simp] lemma prob_event_apply [spec'.finite_range] (e : set (spec.range i × S)) :
  ⦃e | ⟪o | update_state, default_state⟫ i (t, s)⦄ =
    ⦃λ u, (u, update_state s i t u) ∈ e | o i t⦄ :=
by simpa only [apply_eq, prob_event_map]

end prob_event

end distribution_semantics

end tracking_oracle