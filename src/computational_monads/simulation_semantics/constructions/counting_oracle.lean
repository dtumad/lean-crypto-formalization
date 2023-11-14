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
@[inline, reducible] noncomputable def counting_oracle (spec : oracle_spec) :
  sim_oracle spec spec (query_count spec) :=
-- { default_state := ∅,
--   o := λ i ⟨t, qc⟩, query_bind' i t _ (λ u, pure' _ (u, qc.increment i 1)) }
⟪query | λ qc i u t, qc.increment i 1, ∅⟫

notation `countingₛₒ` := counting_oracle _

lemma counting_oracle.def : (counting_oracle spec) =
  ⟪query | λ qc i u t, qc.increment i 1, ∅⟫ := rfl

instance counting_oracle.is_tracking : (counting_oracle spec).is_tracking :=
tracking_oracle.is_tracking query _ ∅

namespace counting_oracle

lemma apply_eq {i : spec.ι} (t : spec.domain i) (qc : spec.query_count) :
  countingₛₒ i (t, qc) = (λ u, (u, qc.increment i 1)) <$> (query i t) := rfl

lemma answer_query_eq : (counting_oracle spec).answer_query = query := rfl

lemma update_state_eq : (counting_oracle spec).update_state = λ qc i t u, qc.increment i 1 := rfl

section simulate'

variables (oa : oracle_comp spec α) (s : spec.query_count)

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' countingₛₒ oa s ≃ₚ oa :=
is_tracking.simulate'_dist_equiv_self countingₛₒ oa s (λ i t, dist_equiv.rfl)

@[simp] lemma support_simulate' : (simulate' countingₛₒ oa s).support = oa.support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_simulate' [decidable_eq α] :
  (simulate' countingₛₒ oa s).fin_support = oa.fin_support :=
by pairwise_dist_equiv

@[simp] lemma eval_dist_simulate' : ⁅simulate' countingₛₒ oa s⁆ = ⁅oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_output_simulate' (x : α) : ⁅= x | simulate' countingₛₒ oa s⁆ = ⁅= x | oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_simulate' (e : set α) : ⁅e | simulate' countingₛₒ oa s⁆ = ⁅e | oa⁆ :=
by pairwise_dist_equiv

end simulate'

end counting_oracle