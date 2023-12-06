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

lemma logging_oracle.def :
  logging_oracle spec = tracking_oracle (λ i t u log, log.log_query i t u) := rfl

instance logging_oracle.is_tracking : (logging_oracle spec).is_tracking :=
tracking_oracle.is_tracking _

namespace logging_oracle

lemma apply_eq {i : spec.ι} (t : spec.domain i) (qc : spec.query_log) :
  loggingₛₒ i (t, qc) = (λ u, (u, qc.log_query i t u)) <$> (query i t) := rfl


-- instance logging_oracle.is_tracking' : (logging_oracle spec).is_tracking' :=
-- { fst_map_apply_eq_query := begin
--   intros i t s,
--   rw [apply_eq, map_map_eq_map_comp, id_map'],
-- end

-- }

-- lemma answer_query_eq : (logging_oracle spec).answer_query = query := rfl

-- lemma update_state_eq : (logging_oracle spec).update_state = query_log.log_query := rfl

-- section simulate'

-- variables (oa : oracle_comp spec α) (s : spec.query_log)

-- @[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' loggingₛₒ oa s ≃ₚ oa :=
-- by pairwise_dist_equiv --is_tracking.simulate'_dist_equiv_self loggingₛₒ oa s (λ i t, dist_equiv.rfl)

-- @[simp] lemma support_simulate' : (simulate' loggingₛₒ oa s).support = oa.support :=
-- by simp

-- @[simp] lemma fin_support_simulate' [decidable_eq α] :
--   (simulate' loggingₛₒ oa s).fin_support = oa.fin_support :=
-- by simp

-- @[simp] lemma eval_dist_simulate' : ⁅simulate' loggingₛₒ oa s⁆ = ⁅oa⁆ :=
-- by pairwise_dist_equiv

-- @[simp] lemma prob_output_simulate' (x : α) : ⁅= x | simulate' loggingₛₒ oa s⁆ = ⁅= x | oa⁆ :=
-- by pairwise_dist_equiv

-- @[simp] lemma prob_event_simulate' (e : set α) : ⁅e | simulate' loggingₛₒ oa s⁆ = ⁅e | oa⁆ :=
-- by pairwise_dist_equiv

-- end simulate'

/-- Simulating with `countingₛₒ` is equivalent to simulating with `loggingₛₒ` and then
reducing the final `query_log` to the associated `query_count` given by `to_query_count`. -/
lemma map_to_query_count_dist_equiv (oa : oracle_comp spec α) (s : spec.query_log) :
  prod.map id indexed_list.to_query_count <$> simulate loggingₛₒ oa s ≃ₚ
    simulate countingₛₒ oa s :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  {
    refl,
  },
  {
    simp [simulate_bind, simulate_query, map_bind],
    rw_dist_equiv [hoa],
    sorry,
  }
  -- induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  -- { rw_dist_equiv [map_return_dist_equiv] },
  -- { simp_rw [simulate_bind],
  --   rw_dist_equiv [map_bind_dist_equiv, hob, symm (hoa _), bind_map_dist_equiv] },
  -- { simp only [simulate_query, tracking_oracle.apply_eq, map_map_eq_map_comp,
  --     indexed_list.coe_query_count_eq],
  --   refine map_dist_equiv_of_dist_equiv' (funext (λ u, _)) dist_equiv.rfl }
end

-- TODO: generalize to other tracking oracles
lemma queries_at_most_simulate (qc : spec.query_count) (oa : oracle_comp spec α)
  (h : oa.queries_at_most qc) (ql : spec.query_log) :
  (simulate loggingₛₒ oa ql).queries_at_most qc :=
begin
  sorry
end

end logging_oracle