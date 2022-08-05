import computational_monads.simulation_semantics.default_simulate

/-!
# Query Counting Simulation Oracle

Defines a simple `counting_oracle` simulation oracle that just counts the number of queries made.
The internal state of the oracle is exactly a `n : ℕ` giving the amount of queries at that point.
This value is always finite as the `oracle_comp` monad doesn't have unbounded recursion.

-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Simulation oracle that just counts the number of queries to the oracles -/
def counting_oracle : simulation_oracle spec spec :=
{ S := ℕ,
  o := λ i ⟨t, n⟩, do { u ← query i t, return ⟨u, n + 1⟩ },
  default_state := 0 }
