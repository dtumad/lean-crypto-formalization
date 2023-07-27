/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec

/-!
# Log for Tracking and Storing Oracle Queries

This file defines a `query_store` structure for tracking oracle outputs during a computation.
-/

/-- Data type representing a log of oracle queries for a given `oracle_spec`,
represented as a function from oracle indices to lists of query input / output pairs. -/
def query_store (spec : oracle_spec) : Type :=
Π (i : spec.ι), list (spec.range i)

namespace query_log

open oracle_spec

variables {spec : oracle_spec}

section empty

/-- Empty log containing no queries -/


end empty

section log_query

def log_query (log : query_log spec) (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) : query_log spec :=
{
  log_fn := λ i', if h : i = i' then h.rec_on ((t, u) :: log i) else log i',
  current_seed := λ i', if i = i' then (log.current_seed i) + 1 else log.current_seed i,
  current_seed_le_length
}

end log_query

end query_log
