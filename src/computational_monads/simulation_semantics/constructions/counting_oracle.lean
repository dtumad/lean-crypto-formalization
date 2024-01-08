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

lemma simulate_of_nat_eq_increment_map_simulate (i : spec.ι) (n : ℕ) :
  simulate countingₛₒ oa (query_count.of_nat i n) =
    (prod.map id (λ qc, query_count.increment qc i n)) <$> (simulate countingₛₒ oa ∅) :=
begin
  sorry,
end

lemma simulate_eq_map_add_left_simulate_empty :
  simulate countingₛₒ oa qc = (prod.map id ((+) qc)) <$> simulate countingₛₒ oa ∅ :=
begin
  -- refine query_count.increment_induction qc _ _,
  -- {
  --   rw [indexed_list.empty_add_eq_id, prod.map_id, id_map],
  -- },
  -- {
  --   intros i n qc hi hqc,
  -- }
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing qc,
  {
    simp [simulate_return],
  },
  {
    simp [simulate_bind, simulate_query],
    simp_rw [oracle_comp.bind_map],
    refine bind_ext_congr (λ u, _),
    simp,
    rw [hoa],
    rw [simulate_of_nat_eq_increment_map_simulate,
      map_map_eq_map_comp, prod.map_comp_map],
    simp [function.comp, query_count.add_increment, ← query_count.increment_add],
    refl,
  }
end

-- lemma simulate_eq_map_add_right_simulate_empty :
--   simulate countingₛₒ oa qc = (prod.map id (+ qc)) <$> simulate countingₛₒ oa ∅ :=
-- begin
--   sorry,
-- end

end counting_oracle