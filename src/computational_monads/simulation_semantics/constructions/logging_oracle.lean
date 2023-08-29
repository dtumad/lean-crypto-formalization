/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_log.basic
import computational_monads.simulation_semantics.is_tracking

/-!
# Logging Oracles

This file defines a `loggingₛₒ` for simulating a computation while logging all queries.
The implementation is as a `tracking_oracle`, using a `query_log` as the internal state to
log the input and output of each query.
-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' spec'' : oracle_spec}

def loggingₛₒ {spec : oracle_spec} : sim_oracle spec spec (query_log spec) :=
⟪query | λ i t u, query_log.log_query i t u, query_log.init spec⟫

namespace loggingₛₒ

end loggingₛₒ