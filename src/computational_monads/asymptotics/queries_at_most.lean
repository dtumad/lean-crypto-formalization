/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.counting_oracle
import data.polynomial.eval

/-!
# Query Bounds for Oracle Computations

This file defines a inductive type for computations making at most some given number of queries.
`queries_at_most oa i n` says that on any run, `oa` makes at most `n` calls to the oracle
corresponding to index `i`, regardless of what the query outputs are.
`query_bound oa` represents a bundled bound on each of the individual queries made.
-/

open oracle_comp oracle_spec

variables {α β : Type} {spec spec' : oracle_spec}

inductive queries_at_most {spec : oracle_spec} (i : spec.ι) :
    Π {α : Type}, oracle_comp spec α → ℕ → Prop
| queries_at_most_pure' {α : Type} (a : α) :
    queries_at_most (pure' α a) 0
| queries_at_most_bind' {α β : Type} (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (p q : ℕ) (hca : queries_at_most oa p) (hcb : ∀ a, queries_at_most (ob a) q) :
    queries_at_most (oa >>= ob) (p + q)
| queries_at_most_query_same_index (t : spec.domain i) :
    queries_at_most (query i t) 1
| queries_at_most_query_diff_index {i' : spec.ι} (h : i ≠ i') (t : spec.domain i') :
    queries_at_most (query i' t) 0
| queries_at_most_trans {α : Type} (oa : oracle_comp spec α) {p q : ℕ}
    (hoa : queries_at_most oa p) (h : p < q) :
    queries_at_most oa q

-- /-- An function `ℕ → oracle_comp` has `polynomial_queries` if the number of queries made
--   has growth bounded by a polynomial in the input `ℕ`. Note that it's a sigma type, not a `Prop`.
--   Used to show that an `oracle_comp` with polynomial time simulated by a polynomial time oracle
--     is still polynomial time if the number of queries is also polynomial -/
-- def polynomial_queries (oa : ℕ → oracle_comp spec α) : Prop :=
-- ∃ (p : polynomial ℕ), ∀ n, queries_at_most (oa n) (p.eval n)