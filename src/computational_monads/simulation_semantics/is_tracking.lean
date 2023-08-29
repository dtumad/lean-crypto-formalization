/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.induction.support
import computational_monads.simulation_semantics.simulate.induction.eval_dist
import computational_monads.simulation_semantics.simulate.subsingleton

/-!
# Tracking Simulation Oracles

This file defines a typeclass `sim_oracle.is_tracking` for oracles in which the
query responses are independent of the current oracle state. For example in `loggingₛₒ`
the internal state doesn't change the input and output, it just records them.
This allows for many lemmas to be automatically shared between these sorts of oracles.
`sim_oracle.is_stateless` extends this further to oracles with no internal state at all.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

open_locale big_operators ennreal
open oracle_comp oracle_spec

namespace sim_oracle

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