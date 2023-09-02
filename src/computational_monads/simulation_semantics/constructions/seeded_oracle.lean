/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_seed.generate_seed
import computational_monads.query_tracking.indexed_list.get_or_else
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
unless it runs out of values in which case it returns a only a partial computation.
If the initial seed is larger than a query bound on the computation it will always finish.
-/

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {α β γ : Type}

/-- Run a computation by using a `query_seed` to answer queries when possible, and making new
queries if there isn't a seed value. If the `query_seed` comes from executing `generate_seed`
then this will give a computation distributionally equivalent to the original computation. -/
def seeded_oracle (spec : oracle_spec) : sim_oracle spec spec (spec.query_seed) :=
{ o := λ i x, indexed_list.get_or_else x.2 i (query i x.1),
  default_state := ∅ }

notation `seededₛₒ` := seeded_oracle _

namespace seeded_oracle

-- TODO

end seeded_oracle