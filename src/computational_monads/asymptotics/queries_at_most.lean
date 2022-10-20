import computational_monads.simulation_semantics.constructions.counting_oracle
import data.polynomial

open oracle_comp oracle_spec

variables {α β : Type} {spec spec' : oracle_spec}

/-- Oracle computations that uniformly make at most a given number of queries.
  In particular `simulate` will call the `sim_oracle` at most that many times -/
inductive queries_at_most : Π {α : Type}, oracle_comp spec α → ℕ → Type 1
| queries_at_most_sample {α : Type} (a : α) :
    queries_at_most (pure a) 0
| queries_at_most_bind' {α β : Type} (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (p q : ℕ) (hca : queries_at_most oa p) (hcb : ∀ a, queries_at_most (ob a) q) :
    queries_at_most (oa >>= ob) (p + q)
| queries_at_most_query {i : spec.ι} (a : spec.domain i) :
    queries_at_most (query i a) 1
| queries_at_most_trans {α : Type} (oa : oracle_comp spec α) {p q : ℕ}
    (hoa : queries_at_most oa p) (h : p ≤ q) :
    queries_at_most oa q

/-- An function `ℕ → oracle_comp` has `polynomial_queries` if the number of queries made
  has growth bounded by a polynomial in the input `ℕ`. Note that it's a sigma type, not a `Prop`.
  Used to show that an `oracle_comp` with polynomial time simulated by a polynomial time oracle
    is still polynomial time if the number of queries is also polynomial -/
def polynomial_queries (oa : ℕ → oracle_comp spec α) : Type 1 :=
Σ (p : polynomial ℕ), ∀ n, queries_at_most (oa n) (p.eval n)