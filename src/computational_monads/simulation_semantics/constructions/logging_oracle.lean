/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_log.basic
import computational_monads.asymptotics.polynomial_queries

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
def logging_oracle (spec : oracle_spec) : sim_oracle spec spec (query_log spec) :=
tracking_oracle (λ i t u log, log.log_query i t u)

notation `loggingₛₒ` := logging_oracle _

instance logging_oracle.is_tracking : (logging_oracle spec).is_tracking :=
tracking_oracle.is_tracking _

namespace logging_oracle

section apply

@[simp] lemma apply_eq {i : spec.ι} (t : spec.domain i) (qc : spec.query_log) :
  loggingₛₒ i (t, qc) = (λ u, (u, qc.log_query i t u)) <$> query i t := rfl

end apply

variables (oa : oracle_comp spec α) (log : spec.query_log)

/-- Simulating with `countingₛₒ` is equivalent to simulating with `loggingₛₒ` and then
reducing the final `query_log` to the associated `query_count` given by `to_query_count`. -/
lemma map_to_query_count (oa : oracle_comp spec α) (log : spec.query_log) :
  prod.map id indexed_list.to_query_count <$> simulate loggingₛₒ oa log =
    simulate countingₛₒ oa log.to_query_count :=
prod_map_id_simulate_eq_simulate _ _ _ (λ i t il, by simp [apply_eq, function.comp]) oa log

lemma simulate_eq_map_add_left_simulate_empty :
  simulate loggingₛₒ oa log = (prod.map id ((+) log)) <$> simulate loggingₛₒ oa ∅ :=
begin
  refine indexed_list.add_values_induction log _ _,
  { rw [indexed_list.empty_add_eq_id, prod.map_id, id_map] },
  { refine λ i n qc hi hqc h, trans (congr_arg _ (symm (indexed_list.add_empty _)))
      (symm (prod_map_id_simulate_eq_simulate loggingₛₒ loggingₛₒ _ (λ i t s, _) _ _)),
    simp [function.comp, query_log.log_query, indexed_list.add_values_add_eq_add_add_values] },
end

end logging_oracle