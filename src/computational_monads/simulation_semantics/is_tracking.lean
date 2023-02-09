/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.support
import computational_monads.simulation_semantics.simulate.eval_dist
import computational_monads.simulation_semantics.simulate.subsingleton
import computational_monads.support.prod

/-!
# Tracking Simulation Oracles

This file defines a typeclass `sim_oracle.is_tracking` for oracles in which the
query responses are independent of the current oracle state. For example in `logging_oracle`
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
`eval_dist_apply` asserts that the oracle behaviour is captured exactly by these two functions. -/
class is_tracking (so : sim_oracle spec spec' S) :=
(query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
(state_f : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
(eval_dist_apply : ∀ (i : spec.ι) (t : spec.domain i) (s : S),
  ⁅so i (t, s)⁆ = ⁅(λ u, (u, state_f s i t u)) <$> query_f i t⁆)

/-- Alias to be able to refer to the query function from the `sim_oracle` namespace. -/
@[inline, reducible] def answer_query (so : sim_oracle spec spec' S) [hso : so.is_tracking]
  (i : spec.ι) (t : spec.domain i) : oracle_comp spec' (spec.range i) := hso.query_f i t

/-- Alias to be able to refer to the state update function from the `sim_oracle` namespace. -/
@[inline, reducible] def update_state (so : sim_oracle spec spec' S) [hso : so.is_tracking]
  (s : S) (i : spec.ι) (t : spec.domain i) (u : spec.range i) : S := hso.state_f s i t u

namespace is_tracking

variables (so : sim_oracle spec spec' S) [hso : so.is_tracking]
  (i : spec.ι) (t t' : spec.domain i) (s s' : S) (u u' : spec.range i)
include hso

section support

lemma support_apply' : (so i (t, s)).support =
  ((λ u, (u, so.update_state s i t u)) <$> so.answer_query i t).support :=
by simp_rw [← support_eval_dist, hso.eval_dist_apply]

@[simp] lemma support_apply : (so i (t, s)).support =
  (λ u, (u, so.update_state s i t u)) '' (so.answer_query i t).support :=
by rw [support_apply', support_map]

end support

section fin_support

variables [∀ i t, (so.o i t).decidable] [∀ i t, (so.answer_query i t).decidable]

lemma fin_support_apply' [decidable_eq S] : (so i (t, s)).fin_support =
  ((λ u, (u, so.update_state s i t u)) <$> so.answer_query i t).fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_apply']

@[simp] lemma fin_support_apply [decidable_eq S] : (so i (t, s)).fin_support =
  (so.answer_query i t).fin_support.image (λ u, (u, so.update_state s i t u)) :=
by rw [fin_support_apply', fin_support_map]

end fin_support

end is_tracking

end sim_oracle