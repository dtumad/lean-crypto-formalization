import computational_monads.simulation_semantics.constructions.tracking_oracle

/-!
# Query Counting Simulation Oracle

Defines a simple `counting_oracle` simulation oracle that just counts the number of queries made.
The internal state of the oracle is exactly a `n : ℕ` giving the amount of queries at that point.
This value is always finite as the `oracle_comp` monad doesn't have unbounded recursion.

-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (n m : ℕ)

/-- Simulation oracle that just counts the number of queries to the oracles -/
def counting_oracle : simulation_oracle spec spec :=
⟪ query | λ n _ _ _, n + 1 , 0 ⟫

namespace counting_oracle

section support

end support

section distribution_semantics

section equiv

end equiv

section prob_event


end prob_event

end distribution_semantics

end counting_oracle
