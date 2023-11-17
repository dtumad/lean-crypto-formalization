/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.subsingleton
import computational_monads.distribution_semantics.mprod

/-!
# Tracking Simulation Oracles

This file defines a typeclass `sim_oracle.is_tracking` for oracles in which the
query responses are independent of the current oracle state.
This is represented by giving functions `query_f` and `state_f` that correspond to these pieces,
and a statement `apply_dist_equiv_state_f_map_query_f` that shows that the oracle function
actually splits into the two components given.

Note that we require that `query_f` be deterministic for simplicity.
For current use cases this is generally sufficient.
Also note that because `query_f` and `state_f` are given explicitly rather than existentially,
`is_tracking` is not a proposition, and in particular two different instances may exist.
Generally it's best to avoid situations with multiple distinct instances.

For example in `loggingₛₒ` the internal state doesn't change the main output, it just records it.
This allows for many lemmas to be automatically shared between these sorts of oracles.
`sim_oracle.is_stateless` extends this further to oracles with no internal state at all.

We also construct a `tracking_oracle` that creates a simulation oracle from a direct specification
of `query_f` and `state_f`, that satisfies `is_tracking` by construction.
This is convenient in defining e.g. `loggingₛₒ` and `idₛₒ`.

TODO: compatibility lemmas for oracle append and compose operations.
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec prod

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace sim_oracle

/-- Typeclass for oracles in which the query responses are independent of the current oracle state.
We define this in terms of the existence of two functions `query_f` and `state_f`
that represent the behaviour of the oracle result and state update respectively.
`apply_dist_equiv_state_f_map_query_f` asserts that the oracle behaviour is captured correctly.

TODO: I think the way to fix the bytecode generation issue is going to be making
tracking oracles an explicit extension of sim oracles, and then making this typeclass one
about existence rather than explicit values? -/
class is_tracking (so : sim_oracle spec spec' S) :=
(query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
(state_f : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
(apply_dist_equiv_state_f_map_query_f : ∀ (i : spec.ι) (t : spec.domain i) (s : S),
  so i (t, s) ≃ₚ (λ u, (u, state_f s i t u)) <$> query_f i t)

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')

/-- Alias to be able to refer to the query function from the `sim_oracle` namespace. -/
@[inline, reducible] def answer_query [hso : so.is_tracking] (i : spec.ι) (t : spec.domain i) :
  oracle_comp spec' (spec.range i) := hso.query_f i t

/-- Alias to be able to refer to the state update function from the `sim_oracle` namespace. -/
@[inline, reducible] def update_state [hso : so.is_tracking] (s : S) (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) : S := hso.state_f s i t u

namespace is_tracking

section apply

variables [hso : so.is_tracking] {i : spec.ι} (t : spec.domain i) (s : S)
include hso

@[pairwise_dist_equiv] lemma apply_dist_equiv : so i (t, s) ≃ₚ
  (λ u, (u, so.update_state s i t u)) <$> so.answer_query i t :=
is_tracking.apply_dist_equiv_state_f_map_query_f i t s

@[simp] lemma support_apply : (so i (t, s)).support =
  (λ u, (u, so.update_state s i t u)) '' (so.answer_query i t).support :=
(apply_dist_equiv so t s).support_eq.trans (by rw [support_map])

@[simp] lemma fin_support_apply [decidable_eq S] : (so i (t, s)).fin_support =
  (so.answer_query i t).fin_support.image (λ u, (u, so.update_state s i t u)) :=
(apply_dist_equiv so t s).fin_support_eq.trans (by rw [fin_support_map])

@[simp] lemma eval_dist_apply : ⁅so i (t, s)⁆ =
  ⁅so.answer_query i t⁆.map (λ u, (u, so.update_state s i t u)) :=
(apply_dist_equiv so t s).eval_dist_eq.trans (by rw [eval_dist_map])

@[simp] lemma prob_output_apply (z : spec.range i × S) : ⁅= z | so i (t, s)⁆ =
  ⁅λ u, (u, so.update_state s i t u) = z | so.answer_query i t⁆ :=
((apply_dist_equiv so t s).prob_output_eq z).trans
  (by simpa only [← prob_event_singleton_eq_prob_output, prob_event_map])

@[simp] lemma prob_event_apply (e : set (spec.range i × S)) : ⁅e | so i (t, s)⁆ =
  ⁅(λ u, (u, so.update_state s i t u)) ⁻¹' e | so.answer_query i t⁆ :=
((apply_dist_equiv so t s).prob_event_eq e).trans (by rw [prob_event_map])

end apply

section simulate_idem

variables [hso : so.is_tracking] (oa : oracle_comp spec α) (s : S)
include hso

/-- If `so.answer_query` can take on any value then the support of simulation with `so` can give
any output that the original computation did (excluding the state). -/
lemma support_simulate'_eq_support
  (h : ∀ i (t : spec.domain i), (so.answer_query i t).support = set.univ) :
  (simulate' so oa s).support = oa.support :=
begin
  refine support_simulate'_eq_support oa s (λ i t s, _),
  rw [is_tracking.support_apply, ← set.image_comp, h],
  exact set.image_univ_of_surjective (λ u, ⟨u, refl u⟩),
end

/-- Version of `support_simulate'_eq_support` for `fin_support`. -/
lemma fin_support_simulate'_eq_fin_support [decidable_eq α]
  (h : ∀ i (t : spec.domain i), (so.answer_query i t).fin_support = finset.univ) :
  (simulate' so oa s).fin_support = oa.fin_support :=
begin
  rw [fin_support_eq_fin_support_iff_support_eq_support],
  refine support_simulate'_eq_support so oa s (λ i t, _),
  rw [← coe_fin_support_eq_support, h i t, finset.coe_univ]
end

/-- If `so.answer_query` looks like just calling `query` then the distribution of the non-state
portion of simulation by `so` is distributionally equivalent to the original computation. -/
lemma simulate'_dist_equiv_self
  (h : ∀ i (t : spec.domain i), so.answer_query i t ≃ₚ query i t) :
  simulate' so oa s ≃ₚ oa :=
begin
  refine simulate'_dist_equiv_self oa s (λ i t s, _),
  rw_dist_equiv [is_tracking.apply_dist_equiv, map_comp_dist_equiv, bind_return_dist_equiv],
  exact h i t,
end

/-- If the distribution of `so.answer_query` is uniform, then the distribution of the first result
of simulation by `so` looks like that of the original computation. -/
lemma eval_dist_simulate'_eq_eval_dist
  (h : ∀ i t, ⁅so.answer_query i t⁆ = pmf.uniform_of_fintype (spec.range i)) :
  ⁅simulate' so oa s⁆ = ⁅oa⁆ :=
is_tracking.simulate'_dist_equiv_self so oa s
  (λ i t, (h i t).trans (eval_dist_query i t).symm)

/-- If all outputs of `so.answer_query` have the same probability, then the first output of
simulation with `so` has the same probability as in the original computation. -/
lemma prob_output_simulate'_eq_prob_output
  (h : ∀ i t u, ⁅= u | so.answer_query i t⁆ = (fintype.card (spec.range i))⁻¹)
  (x : α) : ⁅= x | simulate' so oa s⁆ = ⁅= x | oa⁆ :=
begin
  refine (simulate'_dist_equiv_self so oa s (λ i t, _)).prob_output_eq x,
  simp only [dist_equiv.ext_iff, h, prob_output_query_eq_inv, forall_const],
end

/-- If all outputs of `so.answer_query` have the same probability, then the first output of
simulation with `so` has the same probability as in the original computation. -/
lemma prob_event_simulate'_eq_prob_event
  (h : ∀ i t u, ⁅= u | so.answer_query i t⁆ = (fintype.card (spec.range i))⁻¹)
  (e : set α) : ⁅e | simulate' so oa s⁆ = ⁅e | oa⁆ :=
begin
  refine (simulate'_dist_equiv_self so oa s (λ i t, _)).prob_event_eq e,
  simp only [dist_equiv.ext_iff, h, prob_output_query_eq_inv, forall_const],
end

end simulate_idem

section simulate_eq_simulate

variables [hso : so.is_tracking] [hso' : so'.is_tracking]
  (oa : oracle_comp spec α) (s : S) (s' : S')
include hso hso'

/-- If two tracking oracles answer queries in a way that is distributionally equivalent,
then simulation by either oracle will give the same distribution on the (non-state) output.
TODO: other versions of this for `support`, `eval_dist`, etc. -/
lemma simulate'_dist_equiv_simulate'
  (h : ∀ i t, so.answer_query i t ≃ₚ so'.answer_query i t) :
  simulate' so oa s ≃ₚ simulate' so' oa s' :=
begin
  refine simulate'_dist_equiv_simulate' oa s s' (λ i t s s', _),
  simp_rw_dist_equiv [is_tracking.apply_dist_equiv, map_comp_dist_equiv],
  pairwise_dist_equiv [h i t]
end

end simulate_eq_simulate

end is_tracking

end sim_oracle

/-- Oracle where the query result is indepenent of the current oracle state,
although the new state may depend upon the previous state.
For example a logging oracle that just tracks the input and output of queries.
`o` is the way the oracle responds to queries, which doesn't have access to the state.
`update_state` takes a query and internal state and returns the new internal state.
Note that `update_state` is not a probabalistic function, and has no oracle access -/
def tracking_oracle
  (query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (state_f : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state : S) : sim_oracle spec spec' S :=
{ default_state := default_state,
  o := λ i ⟨t, s⟩, (λ u, (u, state_f s i t u)) <$> (query_f i t) }

notation `⟪` query_f `|` state_f `,` default_state `⟫` :=
  tracking_oracle query_f state_f default_state

instance tracking_oracle.is_tracking
  (query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (state_f : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state : S) : ⟪query_f | state_f, default_state⟫.is_tracking :=
{ query_f := query_f,
  state_f := state_f,
  apply_dist_equiv_state_f_map_query_f := λ i t s, dist_equiv.rfl }

namespace tracking_oracle

variables (query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (state_f : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S) (default_state : S)

@[simp] lemma apply_eq (i : spec.ι) (z : spec.domain i × S) :
  ⟪query_f | state_f, default_state⟫ i z = (λ u, (u, state_f z.2 i z.1 u)) <$> (query_f i z.1) :=
by {cases z, refl}

@[simp] lemma answer_query_eq : ⟪query_f | state_f, default_state⟫.answer_query = query_f := rfl

@[simp] lemma update_state_eq : ⟪query_f | state_f, default_state⟫.update_state = state_f := rfl

end tracking_oracle