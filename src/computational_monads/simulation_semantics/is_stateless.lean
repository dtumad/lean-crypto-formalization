/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_tracking

/-!
# Tracking Simulation Oracles

This file defines a typeclass `sim_oracle.is_stateless` for oracles in which there is no
meaningful internal state, represented by the state type being `subsingleton`.
This is a special case of `sim_oracle.is_tracking`, see `is_stateless.is_tracking`.
This allows for a number of very general lemmas that simplify the process of working
with simulated computations, by automatically removing states.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

open_locale big_operators ennreal
open oracle_comp oracle_spec

namespace sim_oracle

/-- Class to represent oracles that make no use of their internal state.
This class is introduced rather than using a `subsingleton` hypothesis directly
in order to create a unified `is_tracking` instance based on this fact.
This also allows typeclass resolution to work "backwords", in that subsingleton instances don't
have to be defined on the type parameter `S` explicitly, but on the actual oracle instead. -/
class is_stateless (so : sim_oracle spec spec' S) :=
(state_subsingleton : subsingleton S)

variables (so : sim_oracle spec spec' S) (i : spec.ι)
  (t t' : spec.domain i) (s s' : S) (u u' : spec.range i)

/-- Specialize `subsingleton.elim` to simplify the state to the default oracle state.
Usefull for giving a unified convergence point for state values. -/
lemma state_elim [hso : so.is_stateless] (s : S) : s = so.default_state :=
@subsingleton.elim S hso.state_subsingleton s so.default_state

instance is_stateless.is_tracking [hso : so.is_stateless] : so.is_tracking :=
{
  query_f := λ i t, prod.fst <$> so i (t, so.default_state),
  state_f := λ s i t u, so.default_state,
  apply_equiv_state_f_map_query_f :=
    begin
      sorry,
      -- refine λ i t s, trans ((eval_dist_map_id $ (so i (t, s))).symm.trans
      --   (map_equiv_congr (λ x, _) (by rw so.state_elim s))) (eval_dist_map_comp' _ _ _).symm,
      -- simp only [prod.eq_iff_fst_eq_snd_eq, so.state_elim x.2, id.def, eq_self_iff_true, and_self]
    end
}

namespace is_stateless

variable [is_stateless so]

@[simp] lemma answer_query.def : so.answer_query =
  λ i t, prod.fst <$> so i (t, so.default_state) := rfl

@[simp] lemma update_state.def : so.update_state =
  λ s i t u, so.default_state := rfl

section support

lemma support_apply' : (so i (t, s)).support =
  ((λ u, (u, so.default_state)) <$> so.answer_query i t).support :=
by simp only [is_tracking.support_apply', update_state.def]

lemma support_apply : (so i (t, s)).support =
  (λ u, (u, so.default_state)) '' (so.answer_query i t).support :=
by rw [support_apply', support_map]

end support

end is_stateless

end sim_oracle