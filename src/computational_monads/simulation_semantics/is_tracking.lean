/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.subsingleton

/-!
# Tracking Simulation Oracles

This file defines a typeclass `sim_oracle.is_tracking` for oracles in which the
query responses are independent of the current oracle state.
This is represented by giving functions `query_f` and `state_f` that correspond to these pieces,
and a statement `apply_dist_equiv_state_f_map_query_f` that shows that the oracle function
actually splits into the two components given.

For example in `loggingₛₒ` the internal state doesn't change the main output, it just records it.
This allows for many lemmas to be automatically shared between these sorts of oracles.
`sim_oracle.is_stateless` extends this further to oracles with no internal state at all.

We also construct a `tracking_oracle` that creates a simulation oracle from a direct specification
of `query_f` and `state_f`, that satisfies `is_tracking` by construction.
This is convenient in defining e.g. `loggingₛₒ` and `idₛₒ`
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec

namespace sim_oracle

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

/-- Typeclass for oracles in which the query responses are independent of the current oracle state.
We define this in terms of the existence of two functions `query_f` and `state_f`
that represent the behaviour of the oracle result and state update respectively.
`apply_dist_equiv_state_f_map_query_f` asserts that the oracle behaviour is captured correctly. -/
class is_tracking (so : sim_oracle spec spec' S) :=
(query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
(state_f : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
(apply_dist_equiv_state_f_map_query_f : ∀ (i : spec.ι) (t : spec.domain i) (s : S),
  so i (t, s) ≃ₚ (λ u, (u, state_f s i t u)) <$> query_f i t)

variables (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (i : spec.ι)
  (t t' : spec.domain i) (s s' : S) (u u' : spec.range i)

/-- Alias to be able to refer to the query function from the `sim_oracle` namespace. -/
@[inline, reducible] def answer_query [hso : so.is_tracking] (i : spec.ι) (t : spec.domain i) :
  oracle_comp spec' (spec.range i) := hso.query_f i t

/-- Alias to be able to refer to the state update function from the `sim_oracle` namespace. -/
@[inline, reducible] def update_state [hso : so.is_tracking] (s : S) (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) : S := hso.state_f s i t u

namespace is_tracking

variable [hso : so.is_tracking]
include hso

@[pairwise_dist_equiv] lemma apply_dist_equiv : so i (t, s) ≃ₚ
  (λ u, (u, so.update_state s i t u)) <$> so.answer_query i t :=
is_tracking.apply_dist_equiv_state_f_map_query_f i t s

section support

lemma support_apply' : (so i (t, s)).support =
  ((λ u, (u, so.update_state s i t u)) <$> so.answer_query i t).support :=
by simp_rw [← support_eval_dist, (hso.apply_dist_equiv_state_f_map_query_f _ _ _).eval_dist_eq]

@[simp] lemma support_apply : (so i (t, s)).support =
  (λ u, (u, so.update_state s i t u)) '' (so.answer_query i t).support :=
by rw [support_apply', support_map]

end support

section fin_support

lemma fin_support_apply' [decidable_eq S] : (so i (t, s)).fin_support =
  ((λ u, (u, so.update_state s i t u)) <$> so.answer_query i t).fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_apply']

@[simp] lemma fin_support_apply [decidable_eq S] : (so i (t, s)).fin_support =
  (so.answer_query i t).fin_support.image (λ u, (u, so.update_state s i t u)) :=
by rw [fin_support_apply', fin_support_map]

end fin_support

section eval_dist

lemma eval_dist_apply' : ⁅so i (t, s)⁆ =
  ⁅(λ u, (u, so.update_state s i t u)) <$> so.answer_query i t⁆ :=
apply_dist_equiv_state_f_map_query_f i t s

@[simp] lemma eval_dist_apply : ⁅so i (t, s)⁆ =
  ⁅so.answer_query i t⁆.map (λ u, (u, so.update_state s i t u)) :=
by rw [eval_dist_apply', eval_dist_map]

end eval_dist

section prob_event

lemma prob_event_apply' (e : set (spec.range i × S)) : ⁅e | so i (t, s)⁆ =
  ⁅e | (λ u, (u, so.update_state s i t u)) <$> so.answer_query i t⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_apply' so i t s) e

@[simp] lemma prob_event_apply (e : set (spec.range i × S)) : ⁅e | so i (t, s)⁆ =
  ⁅(λ u, (u, so.update_state s i t u)) ⁻¹' e | so.answer_query i t⁆ :=
by rw [prob_event_apply', prob_event_map]

end prob_event

section simulate'

/-- If the oracle can take on any value then the first element of the support is unchanged -/
lemma support_simulate'_eq_support (h : ∀ i t, (so.answer_query i t).support = set.univ) :
  (simulate' so oa s).support = oa.support :=
sorry
-- support_simulate'_eq_support _ oa s (λ i t s, set.ext (λ x, by simp_rw [is_tracking.support_apply,
--   set.image_image, h, set.image_univ, set.range_id', set.top_eq_univ]))

lemma fin_support_simulate'_eq_fin_support
  (h : ∀ i t, (so.answer_query i t).fin_support = finset.univ) :
  (simulate' so oa s).fin_support = oa.fin_support :=
begin
  rw [fin_support_eq_fin_support_iff_support_eq_support],
  refine support_simulate'_eq_support so oa s (λ i t, _),
  rw [← coe_fin_support_eq_support, h i t, finset.coe_univ]
end

lemma simulate'_dist_equiv_self (h : ∀ i t, so.answer_query i t ≃ₚ query i t) :
  simulate' so oa s ≃ₚ oa :=
begin
  sorry,
  -- refine simulate'_dist_equiv_s
end


lemma eval_dist_simulate'_eq_eval_dist
  (h : ∀ i t, ⁅so.answer_query i t⁆ = pmf.uniform_of_fintype (spec.range i)) :
  ⁅simulate' so oa s⁆ = ⁅oa⁆ :=
begin
  sorry,
  -- refine eval_dist_simulate'_eq_eval_dist so oa s (λ i t s, _),
end

end simulate'

end is_tracking

end sim_oracle

/-- Oracle where the query result is indepenent of the current oracle state,
although the new state may depend upon the previous state.
For example a logging oracle that just tracks the input and output of queries.
`o` is the way the oracle responds to queries, which doesn't have access to the state.
`update_state` takes a query and internal state and returns the new internal state.
Note that `update_state` is not a probabalistic function, and has no oracle access -/
def tracking_oracle {spec spec' : oracle_spec} {S : Type}
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state : S) : sim_oracle spec spec' S :=
{ default_state := default_state,
  o := λ i ⟨t, s⟩, (λ u, (u, update_state s i t u)) <$> (o i t) }

notation `⟪` o `|` update_state `,` default_state `⟫` :=
  tracking_oracle o update_state default_state

namespace tracking_oracle

open_locale big_operators ennreal
open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' spec'' : oracle_spec}
variables {S S' : Type} (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (update_state' : Π (s : S') (i : spec.ι), spec.domain i → spec.range i → S')
  (default_state : S) (default_state' : S') (a : α) (i : spec.ι) (t : spec.domain i)
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s : S) (s' : S')
  (x : spec.domain i × S) (y : spec.range i × S)

@[simp] lemma apply_eq : ⟪o | update_state, default_state⟫ i x =
  (λ u, (u, update_state x.2 i x.1 u)) <$> (o i x.1) := by {cases x, refl}

section support

@[simp] lemma support_apply : (⟪o | update_state, default_state⟫ i x).support =
  (λ u, (u, update_state x.2 i x.1 u)) '' (o i x.1).support :=
set.ext (λ y, by rw [apply_eq, support_map])

lemma fin_support_apply [decidable_eq S] :
  (⟪o | update_state, default_state⟫ i x).fin_support =
    (o i x.1).fin_support.image (λ u, (u, update_state x.2 i x.1 u)) :=
by simp only [fin_support_eq_iff_support_eq_coe, apply_eq, support_map,
  finset.coe_image, coe_fin_support_eq_support]

lemma mem_support_apply_iff {y : spec.range i × S} :
  y ∈ (⟪o | update_state, default_state⟫ i x).support ↔
    y.1 ∈ (o i x.1).support ∧ update_state x.2 i x.1 y.1 = y.2 :=
by simp only [support_apply, prod.eq_iff_fst_eq_snd_eq, set.mem_image,
  and_comm (_ = y.fst), exists_eq_right_right]

/-- If the oracle can take on any value then the first element of the support is unchanged -/
lemma support_simulate'_eq_support (h : ∀ i t, (o i t).support = ⊤) :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support = oa.support :=
sorry
-- support_simulate'_eq_support _ oa s (λ i t s, set.ext (λ x, by simp only
--   [h, set.top_eq_univ, set.mem_univ, true_and, apply_eq, support_map, set.mem_image,
--     prod.exists, prod.mk.inj_iff, exists_eq_left, exists_eq_left', exists_apply_eq_apply]))

/-- Particular case of `support_simulate'_eq_support` for `query`.
In particular a tracking oracle that *only* does tracking doesn't affect the main output. -/
@[simp] lemma support_simulate'_query_eq_support :
  (simulate' ⟪query | update_state, default_state⟫ oa s).support = oa.support :=
support_simulate'_eq_support query update_state default_state oa s (λ _ _, rfl)

lemma support_simulate'_eq_support_simulate' (h : ∀ i t, (o i t).support = (o' i t).support) :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support =
    (simulate' ⟪o' | update_state', default_state'⟫ oa s').support :=
support_simulate'_eq_support_simulate' oa s s' (λ i t s s', set.ext (λ x,
  by simp only [mem_support_apply_iff, h, simulate'_query, support_map, support_apply,
    set.mem_image, set.mem_set_of_eq, prod.exists, exists_and_distrib_right, exists_eq_right,
    exists_eq_right', exists_eq_right_right, prod.eq_iff_fst_eq_snd_eq, and_comm (_ = x)]))

/-- The support of `simulate'` is independt of the tracking functions -/
lemma support_simulate'_eq_support_simulate'_of_oracle_eq :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support =
    (simulate' ⟪o | update_state', default_state'⟫ oa s').support :=
support_simulate'_eq_support_simulate' o o _ _ _ _ oa s s' (λ _ _, rfl)

section subsingleton

variables [subsingleton S]

@[simp] lemma support_apply_of_subsingleton :
  (⟪o | update_state, default_state⟫ i x).support = prod.fst ⁻¹' (o i x.1).support :=
set.ext (λ y, by erw [apply_eq, map_eq_bind_return_comp,
  support_bind_prod_mk_of_snd_subsingleton, set.image_id])

lemma support_simulate_eq_preimage_support_of_subsingleton (h : ∀ i t, (o i t).support = ⊤) :
  (simulate ⟪o | update_state, default_state⟫ oa s).support = prod.fst ⁻¹' oa.support :=
by rw [set.preimage, support_simulate_eq_support_simulate'_of_subsingleton,
  support_simulate'_eq_support o _ _ oa s h]

@[simp] lemma support_simulate_query_eq_support_of_subsingleton :
  (simulate ⟪query | update_state, default_state⟫ oa s).support = prod.fst ⁻¹' oa.support :=
support_simulate_eq_preimage_support_of_subsingleton query _ _ oa s (λ _ _, rfl)

end subsingleton

end support

section eval_dist

@[simp] lemma eval_dist_apply :
  ⁅⟪o | update_state, default_state⟫ i (t, s)⁆ = ⁅o i t⁆.map (λ u, (u, update_state s i t u)) :=
by rw [apply_eq, eval_dist_map]

/-- If the oracle has uniform distribution, then the distribution under `simulate'` is unchanged -/
lemma eval_dist_simulate'_eq_eval_dist
  (h : ∀ i t, ⁅o i t⁆ = pmf.uniform_of_fintype (spec.range i)) :
  ⁅simulate' ⟪o | update_state, default_state⟫ oa s⁆ = ⁅oa⁆ :=
sorry
-- eval_dist_simulate'_eq_eval_dist _ oa s (λ i t s, trans
--   (by simpa [eval_dist_apply, pmf.map_comp] using pmf.map_id ⁅o i t⁆) (h i t))

/-- Specific case of `eval_dist_simulate'_eq_eval_dist` for query.
In particular if a tracking oracle *only* does tracking gives the same main output distribution. -/
@[simp] lemma eval_dist_simulate'_query_eq_eval_dist :
  ⁅simulate' ⟪query | update_state, default_state⟫ oa s⁆ = ⁅oa⁆ :=
eval_dist_simulate'_eq_eval_dist query update_state default_state oa s (λ _ _, rfl)

lemma eval_dist_simulate'_eq_eval_dist_simulate'
  (h : ∀ i t, o i t ≃ₚ o' i t) : simulate' ⟪o | update_state, default_state⟫ oa s ≃ₚ
    simulate' ⟪o' | update_state', default_state'⟫ oa s' :=
sorry
-- -- eval_dist_simulate'_eq_eval_dist_simulate' (λ i t s s',
--   by simp [pmf.map_comp, tracking_oracle.apply_eq, eval_dist_map, (h i t).eval_dist_eq]) _ _ _

/-- The first output of simulation under different `tracking_oracle` with the same oracle
is the same regardless of if the tracking functions are different. -/
lemma eval_dist_simulate'_eq_eval_dist_simulate'_of_oracle_eq :
  ⁅simulate' ⟪o | update_state, default_state⟫ oa s⁆ =
    ⁅simulate' ⟪o | update_state', default_state'⟫ oa s'⁆ :=
eval_dist_simulate'_eq_eval_dist_simulate' o o _ _ _ _ oa s s' (λ _ _, rfl)

end eval_dist

section prob_event

variable (e : set α)

@[simp] lemma prob_event_apply (e : set (spec.range i × S)) :
  ⁅e | ⟪o | update_state, default_state⟫ i (t, s)⁆ =
    ⁅λ u, (u, update_state s i t u) ∈ e | o i t⁆ :=
by simpa only [apply_eq, prob_event_map]

lemma prob_event_simulate'_eq_prob_event
  (h : ∀ i t, ⁅o i t⁆ = pmf.uniform_of_fintype (spec.range i)) :
  ⁅e | simulate' ⟪o | update_state, default_state⟫ oa s⁆ = ⁅e | oa⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_simulate'_eq_eval_dist _ _ _ _ _ h) e

/-- Specific case of `eval_dist_simulate'_eq_eval_dist` for query.
In particular if a tracking oracle *only* does tracking gives the same main output distribution. -/
lemma prob_event_simulate'_query_eq_prob_event :
  ⁅e | simulate' ⟪query | update_state, default_state⟫ oa s⁆ = ⁅e | oa⁆ :=
prob_event_simulate'_eq_prob_event _ _ _ oa s e (λ _ _, rfl)

lemma prob_event_simulate'_eq_prob_event_simulate'
  (h : ∀ i t, o i t ≃ₚ o' i t) : ⁅e | simulate' ⟪o | update_state, default_state⟫ oa s⁆ =
    ⁅e | simulate' ⟪o' | update_state', default_state'⟫ oa s'⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_simulate'_eq_eval_dist_simulate' _ _ _ _ _ _ _ _ _ h) e

/-- The first output of simulation under different `tracking_oracle` with the same oracle
is the same regardless of if the tracking functions are different. -/
lemma prob_event_simulate'_eq_eval_dist_simulate'_of_oracle_eq :
  ⁅e | simulate' ⟪o | update_state, default_state⟫ oa s⁆ =
    ⁅e | simulate' ⟪o | update_state', default_state'⟫ oa s'⁆ :=
prob_event_simulate'_eq_prob_event_simulate' o o _ _ _ _ oa s s' e (λ _ _, rfl)

end prob_event

end tracking_oracle