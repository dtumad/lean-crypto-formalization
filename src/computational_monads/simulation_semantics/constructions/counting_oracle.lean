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

lemma mem_support_apply_iff {i} (t : spec.domain i) (qc : spec.query_count)
  (z : spec.range i × spec.query_count) :
  z ∈ (countingₛₒ i (t, qc)).support ↔ qc.increment i 1 = z.2 :=
by simp [prod.eq_iff_fst_eq_snd_eq]

variables (oa : oracle_comp spec α) (qc : spec.query_count)

lemma simulate'_eq : simulate' countingₛₒ oa qc = oa :=
is_tracking.simulate'_eq_self countingₛₒ oa qc

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' countingₛₒ oa qc ≃ₚ oa :=
is_tracking.simulate'_dist_equiv_self countingₛₒ oa qc

lemma simulate_increment_eq_increment_map_simulate (i : spec.ι) (n : ℕ) :
  simulate countingₛₒ oa (qc.increment i n) =
    (prod.map id (λ qc, query_count.increment qc i n)) <$> simulate countingₛₒ oa qc :=
begin
  induction oa using oracle_comp.induction_on' with α a j t α oa hoa generalizing qc n i,
  { simp only [simulate_return, map_pure, prod.map_mk, id.def] },
  { simp only [simulate_bind, simulate_query, oracle_comp.bind_map, apply_eq,
      oracle_comp.map_bind, function.comp_app],
    refine bind_ext_congr (λ k, _),
    rw [function.comp_app, query_count.increment_increment_comm, hoa] }
end

lemma simulate_eq_map_add_left_simulate_empty :
  simulate countingₛₒ oa qc = (prod.map id ((+) qc)) <$> simulate countingₛₒ oa ∅ :=
begin
  refine query_count.increment_induction qc _ _,
  { rw [indexed_list.empty_add_eq_id, prod.map_id, id_map] },
  { intros i n qc hi hqc,
    simp_rw [simulate_increment_eq_increment_map_simulate, hqc, map_map_eq_map_comp,
      prod.map_comp_map, function.comp.right_id, function.comp, ← query_count.increment_add] }
end

lemma simulate_eq_map_add_right_simulate_empty :
  simulate countingₛₒ oa qc = (prod.map id (+ qc)) <$> simulate countingₛₒ oa ∅ :=
by simpa only [add_comm _ qc] using simulate_eq_map_add_left_simulate_empty oa qc

end counting_oracle