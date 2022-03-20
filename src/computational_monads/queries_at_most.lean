import computational_monads.oracle_comp

open oracle_comp oracle_comp_spec

variables {A : Type} {spec spec' : oracle_comp_spec}

/-- Oracle computations that uniformly make at most a given number of queries.
  In particular `simulate` will always the `simulation_oracle` at most that many times -/
inductive queries_at_most : Π {A : Type}, oracle_comp spec A → ℕ → Type 1
| queries_at_most_sample {A : Type} (a : A) :
    queries_at_most (pure' A a) 0
| queries_at_most_bind' {A B : Type} (ca : oracle_comp spec A) (cb : A → oracle_comp spec B)
    (p q : ℕ) (hca : queries_at_most ca p) (hcb : ∀ a, queries_at_most (cb a) q) :
    queries_at_most (bind' A B ca cb) (p + q)
| queries_at_most_query {i : spec.ι} (a : spec.domain i) :
    queries_at_most (query i a) 1 

def count_oracle_queries : simulation_oracle spec spec :=
{ S := ℕ,
  o := λ i ⟨t, n⟩, do { u ← query i t, return ⟨u, n + 1⟩ } }

/-- Soundness of `queries_at_most` with respect to simulation -/
theorem queries_at_most_sound (oa : oracle_comp spec A)
  (x : A × ℕ) (hx : x ∈ (simulate count_oracle_queries oa nat.zero).support)
  (n : ℕ) (hn : queries_at_most oa n) : x.2 ≤ n :=
sorry