/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.query_log.basic
import computational_monads.simulation_semantics.constructions.tracking_oracle

/-!
# Logging Oracles

This file defines a `logging_oracle` for simulating a computation while logging all queries.
The implementation is as a `tracking_oracle`, using a `query_log` as the internal state to
log the input and output of each query.
-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} 
  
def logging_oracle (spec : oracle_spec) : sim_oracle spec spec (query_log spec) :=
⟪query | λ i t u, query_log.log_query i t u, query_log.init spec⟫

namespace logging_oracle

variables (a : α) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (i : spec.ι)
  (t : spec.domain i) (log : query_log spec)

@[simp] lemma apply : (logging_oracle spec) i (t, log) =
  query i t >>= λ u, return (u, log.log_query i t u) := rfl

section simulate

lemma simulate_return : simulate (logging_oracle _) (return a) log = return ⟨a, log⟩ := rfl

lemma simulate_query : simulate (logging_oracle _) (query i t) log =
  do {u ← query i t, return (u, log.log_query i t u)} := rfl

lemma simulate_bind : simulate (logging_oracle _) (oa >>= ob) log =
  (simulate (logging_oracle _) oa log) >>= (λ x, simulate (logging_oracle _) (ob x.1) x.2) := rfl

end simulate

section support

@[simp] lemma support_simulate' : (simulate' (logging_oracle spec) oa log).support = oa.support :=
sorry --tracking_oracle.support_simulate'_query_oracle_eq_support _ _ oa log

lemma support_default_simulate' :
  (default_simulate' (logging_oracle spec) oa).support = oa.support :=
support_simulate' oa (query_log.init spec)

end support

section distribution_semantics

open distribution_semantics

section eval_dist

@[simp] lemma eval_dist_simulate' : ⁅simulate' (logging_oracle spec) oa log⁆ = ⁅oa⁆ :=
tracking_oracle.eval_dist_simulate'_query_eq_eval_dist _ _ oa log

lemma eval_dist_default_simulate' : ⁅default_simulate' (logging_oracle spec) oa⁆ = ⁅oa⁆ :=
logging_oracle.eval_dist_simulate' oa (query_log.init spec)

end eval_dist

end distribution_semantics

end logging_oracle