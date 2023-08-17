/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.order

/-!
# Log for Tracking and Storing Oracle Queries

This file defines a `query_seed` structure for tracking oracle outputs during a computation.
-/

namespace oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- Data type representing a seed of oracle query outputs for a given `oracle_spec`,
represented as a function from oracle indices to lists of query outputs,
extending `query_count` such that the count gives the length of the seed. -/
@[inline, reducible] def query_seed (spec : oracle_spec) :=
spec.indexed_list spec.range

namespace query_seed

variables (qs qs' qs'' : spec.query_seed)

section seed_differs

/-- The `n`th seed values differ between `qs` and `qs'`. -/
def seed_differs (qs qs' : spec.query_seed) (i : spec.ι) (n : ℕ) : Prop :=
(qs i).nth n ≠ (qs' i).nth n

end seed_differs

end query_seed

end oracle_spec