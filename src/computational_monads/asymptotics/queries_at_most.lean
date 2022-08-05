import computational_monads.simulation_semantics.default_simulate
import computational_monads.simulation_semantics.constructions.counting_oracle
import data.polynomial

open oracle_comp oracle_spec

variables {A : Type} {spec spec' : oracle_spec}

/-- Oracle computations that uniformly make at most a given number of queries.
  In particular `simulate` will call the `simulation_oracle` at most that many times -/
inductive queries_at_most : Π {A : Type}, oracle_comp spec A → ℕ → Type 1
| queries_at_most_sample {A : Type} (a : A) :
    queries_at_most (pure' A a) 0
| queries_at_most_bind' {A B : Type} (ca : oracle_comp spec A) (cb : A → oracle_comp spec B)
    (p q : ℕ) (hca : queries_at_most ca p) (hcb : ∀ a, queries_at_most (cb a) q) :
    queries_at_most (bind' A B ca cb) (p + q)
| queries_at_most_query {i : spec.ι} (a : spec.domain i) :
    queries_at_most (query i a) 1 

-- /-- Soundness of `queries_at_most` with respect to simulation -/
-- theorem queries_at_most_sound (oa : oracle_comp spec A)
--   (x : A × ℕ) (hx : x ∈ (default_simulate counting_oracle oa).support)
--   (n : ℕ) (hn : queries_at_most oa n) : x.2 ≤ n :=
-- begin

-- end

/-- An function `ℕ → oracle_comp` has `polynomial_queries` if the number of queries made
  has growth bounded by a polynomial in the input `ℕ`. Note that it's a sigma type, not a `Prop`.
  Used to show that an `oracle_comp` with polynomial time simulated by a polynomial time oracle
    is still polynomial time if the number of queries is also polynomial -/
def polynomial_queries (oa : ℕ → oracle_comp spec A) : Type 1 :=
Σ (p : polynomial ℕ), ∀ n, queries_at_most (oa n) (p.eval n)