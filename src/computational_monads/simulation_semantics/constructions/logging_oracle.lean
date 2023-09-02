/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_log.basic
import computational_monads.simulation_semantics.is_tracking

/-!
# Logging Oracles

This file defines a tracking oracle `logging_oracle` for logging all queries during execution.
The implementation is as a `tracking_oracle`, using a `query_log` as the internal state,
preserving the original query calls for the actual oracle responses.
-/

open oracle_comp oracle_spec sim_oracle

variables {α β γ : Type} {spec : oracle_spec}

/-- Simulation oracle for logging the queries made during the computation,
tracked via a `query_log`, whithout modifying the query calls themselves. -/
@[inline, reducible] def logging_oracle (spec : oracle_spec) :
  sim_oracle spec spec (query_log spec) :=
⟪query | query_log.log_query, ∅⟫

notation `loggingₛₒ` := logging_oracle _

lemma logging_oracle.def : logging_oracle spec = ⟪query | query_log.log_query, ∅⟫ := rfl

instance logging_oracle.is_tracking : (logging_oracle spec).is_tracking :=
tracking_oracle.is_tracking query query_log.log_query ∅

namespace logging_oracle

lemma apply_eq {i : spec.ι} (t : spec.domain i) (qc : spec.query_log) :
  loggingₛₒ i (t, qc) = (λ u, (u, qc.log_query i t u)) <$> (query i t) := rfl

lemma answer_query_eq : (logging_oracle spec).answer_query = query := rfl

lemma update_state_eq : (logging_oracle spec).update_state = query_log.log_query := rfl

section simulate'

variables (oa : oracle_comp spec α) (s : spec.query_log)

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' loggingₛₒ oa s ≃ₚ oa :=
is_tracking.simulate'_dist_equiv_self loggingₛₒ oa s (λ i t, dist_equiv.rfl)

@[simp] lemma support_simulate' : (simulate' loggingₛₒ oa s).support = oa.support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_simulate' : (simulate' loggingₛₒ oa s).fin_support = oa.fin_support :=
by pairwise_dist_equiv

@[simp] lemma eval_dist_simulate' : ⁅simulate' loggingₛₒ oa s⁆ = ⁅oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_output_simulate' (x : α) : ⁅= x | simulate' loggingₛₒ oa s⁆ = ⁅= x | oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_simulate' (e : set α) : ⁅e | simulate' loggingₛₒ oa s⁆ = ⁅e | oa⁆ :=
by pairwise_dist_equiv

end simulate'

end logging_oracle