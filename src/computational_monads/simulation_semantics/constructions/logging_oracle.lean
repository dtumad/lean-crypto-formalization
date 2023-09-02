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

open oracle_comp oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- Simulation oracle for logging the queries made during the computation,
tracked via a `query_log`, whithout modifying the query calls themselves. -/
def logging_oracle (spec : oracle_spec) : sim_oracle spec spec (query_log spec) :=
⟪query | query_log.log_query, ∅⟫

notation `loggingₛₒ` := logging_oracle _

instance logging_oracle.is_tracking : (logging_oracle spec).is_tracking :=
tracking_oracle.is_tracking query query_log.log_query ∅

namespace logging_oracle

-- TODO

end logging_oracle