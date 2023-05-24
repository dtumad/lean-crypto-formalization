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
`queries_at_most oa n` says that on any run, `oa` makes at most `n` calls to the oracle,
regardless of what the query outputs are.

`polynomial_queries oa` says that there is some polynomial bounding the number of computations
made by the computation `oa`
-/

open oracle_comp oracle_spec

variables {α β : Type} {spec spec' : oracle_spec}

/-- Oracle computations that uniformly make at most a given number of queries.
In particular `simulate` will call the `sim_oracle` at most that many times.
TODO: This is difficult to work with using `↔` instead of `→`. -/
inductive queries_at_most : Π {α : Type}, oracle_comp spec α → ℕ → Prop
| queries_at_most_pure' {α : Type} (a : α) :
    queries_at_most (pure' α a) 0
| queries_at_most_bind' {α β : Type} (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (p q : ℕ) (hca : queries_at_most oa p) (hcb : ∀ a, queries_at_most (ob a) q) :
    queries_at_most (oa >>= ob) (p + q)
| queries_at_most_query {i : spec.ι} (t : spec.domain i) :
    queries_at_most (query i t) 1
| queries_at_most_trans {α : Type} (oa : oracle_comp spec α) {p q : ℕ}
    (hoa : queries_at_most oa p) (h : p < q) :
    queries_at_most oa q

-- lemma queries_at_most_return_iff (x : α) (n : ℕ) :
--     queries_at_most (return x : oracle_comp spec α) n ↔ n = 0 :=
-- begin
--     refine ⟨λ h, _, λ h, _⟩,
--     {

--         induction h,
--         {
--             refl,
--         },
--         {
--             -- simp at h_ih_hcb,
--             specialize h_ih_hcb (h_oa.default_result),
--             rw [h_ih_hca, h_ih_hcb],
--         },
--         {

--         }
--     },
--     {
--         rw h,
--         apply queries_at_most.queries_at_most_pure',
--     }
-- end

/-- An function `ℕ → oracle_comp` has `polynomial_queries` if the number of queries made
  has growth bounded by a polynomial in the input `ℕ`. Note that it's a sigma type, not a `Prop`.
  Used to show that an `oracle_comp` with polynomial time simulated by a polynomial time oracle
    is still polynomial time if the number of queries is also polynomial -/
def polynomial_queries (oa : ℕ → oracle_comp spec α) : Prop :=
∃ (p : polynomial ℕ), ∀ n, queries_at_most (oa n) (p.eval n)