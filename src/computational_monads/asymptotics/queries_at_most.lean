/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.counting_oracle
import data.polynomial.eval

/-!
# Query Bounds for Oracle Computations

-/

namespace oracle_comp

open oracle_spec

variables {α β : Type} {spec spec' : oracle_spec}

/-- A `query_count` bounds the number of queries made by a computation if any result of simulating
with `countingₛₒ produces a count that is smaller. -/
def queries_at_most (oa : oracle_comp spec α) (qc : spec.query_count) : Prop :=
∀ x qc', (x, qc') ∈ (simulate countingₛₒ oa ∅).support → qc' ≤ qc

end oracle_comp

-- /-- An function `ℕ → oracle_comp` has `polynomial_queries` if the number of queries made
--   has growth bounded by a polynomial in the input `ℕ`. Note that it's a sigma type, not a `Prop`.
--   Used to show that an `oracle_comp` with polynomial time simulated by a polynomial time oracle
--     is still polynomial time if the number of queries is also polynomial -/
-- def polynomial_queries (oa : ℕ → oracle_comp spec α) : Prop :=
-- ∃ (p : polynomial ℕ), ∀ n, queries_at_most (oa n) (p.eval n)