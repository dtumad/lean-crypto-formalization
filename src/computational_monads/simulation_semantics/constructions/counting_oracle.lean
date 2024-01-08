/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_tracking
import computational_monads.query_tracking.query_count.order

/-!
# Query Counting Simulation Oracle

Defines a simple `counting_oracle` simulation oracle that just counts the number of queries made.
The internal state of the oracle is exactly a `n : ℕ` giving the amount of queries at that point.
This value is always finite as the `oracle_comp` monad doesn't have unbounded recursion.
-/

open oracle_comp oracle_spec sim_oracle

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Simulation oracle for counting the queries made during the computation,
tracked via a `query_count`, whithout modifying the query calls themselves. -/
def counting_oracle (spec : oracle_spec) : sim_oracle spec spec (query_count spec) :=
tracking_oracle (λ i t u qc, qc.increment i 1)

notation `countingₛₒ` := counting_oracle _

instance counting_oracle.is_tracking : (counting_oracle spec).is_tracking :=
tracking_oracle.is_tracking _

namespace counting_oracle

@[simp] lemma apply_eq {i : spec.ι} (t : spec.domain i) (qc : spec.query_count) :
  countingₛₒ i (t, qc) = (λ u, (u, qc.increment i 1)) <$> (query i t) := rfl

variables (oa : oracle_comp spec α) (qc : spec.query_count)

lemma simulate'_eq : simulate' countingₛₒ oa qc = oa :=
is_tracking.simulate'_eq_self countingₛₒ oa qc

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' countingₛₒ oa qc ≃ₚ oa :=
is_tracking.simulate'_dist_equiv_self countingₛₒ oa qc

end counting_oracle