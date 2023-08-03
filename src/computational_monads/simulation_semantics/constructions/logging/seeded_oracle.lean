/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_seed.generate_seed
import computational_monads.simulation_semantics.oracle_compose

/-!
# Seeded Simulation Oracle

This file constructs a simulation oracle that allows for a set of predetermined query responses.
The oracle takes a `query_log` as an initial state, and uses the internal values
  to respond to queries, and then forwards any additional queries back to the original oracle.
Note that if any query fails to find a seed value, the entire `query_log` is discarded,
  regardless of if further values exist for oracles of different indices.

This can more generally be thought of as a form of small-step semantics for `oracle_comp`,
  evaluating the computation using the provided value, eventually reducing to a single value,
  unless it runs out of "gas", leading to only a partial evaluation.

-/

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {α β γ : Type}

/-- Use the first element of the `seed` as the query result if inputs match.
  If the query values don't match then throw away the seed as computation has diverged.
  Using this with a log from a previous computation ensures they behave identically. -/
def seeded_oracle {spec : oracle_spec} : sim_oracle spec spec (query_seed spec) :=
{ o := λ i x, query_seed.get_or_else x.2 i x.1,
  default_state := ∅ }

namespace seeded_oracle

@[simp] lemma seeded_oracle_apply (i : spec.ι) (x : spec.domain i × query_seed spec) :
  seeded_oracle i x = query_seed.get_or_else x.2 i x.1 := rfl

end seeded_oracle