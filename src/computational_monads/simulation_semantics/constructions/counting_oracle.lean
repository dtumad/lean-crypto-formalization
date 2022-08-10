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
def counting_oracle (spec : oracle_spec) : simulation_oracle spec spec :=
⟪ query | λ n _ _ _, n + 1 , 0 ⟫

namespace counting_oracle

lemma apply (i : spec.ι) (t : spec.domain i) (n : ℕ) :
  (counting_oracle spec).o i (t, n) = do { u ← query i t, pure (u, (n + 1 : ℕ)) } := rfl

section support

lemma support_apply (i : spec.ι) (t : spec.domain i) (n : ℕ) :
  ((counting_oracle spec).o i (t, n)).support = {x | x.2 = nat.succ n} :=
(tracking_oracle.support_apply query _ _ i t n).trans
  (by simpa only [support_query, set.top_eq_univ, set.mem_univ, true_and])

end support

section distribution_semantics

section equiv

end equiv

section prob_event


end prob_event

end distribution_semantics

end counting_oracle
