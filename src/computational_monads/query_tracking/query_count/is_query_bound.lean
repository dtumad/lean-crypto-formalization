/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.order
import computational_monads.simulation_semantics.constructions.counting_oracle

/-!
# Bounding the Number of Queries by a Computation

This file defines a predicate `is_query_bound oa qb` to represent the fact that
the computation `oa` makes at most as many queries as in the given `query_count`.

See `sec_adv` for computations bundled with a bound on their query count.
-/

namespace oracle_comp

open oracle_spec prod (fst) (snd)

variables {spec : oracle_spec} {α β γ : Type}

/-- `is_query_bound oa qb` means that for each index `i : spec.ι`,
`oa` makes at most `qb.get_count i` calls to the corresponding oracle. -/
def is_query_bound (oa : oracle_comp spec α) (qb : spec.query_count) : Prop :=
∀ z ∈ (simulate countingₛₒ oa ∅).support, snd z ≤ qb

variables (qb : spec.query_count)

lemma is_query_bound_iff_forall (oa : oracle_comp spec α) : is_query_bound oa qb ↔
  ∀ z ∈ (simulate countingₛₒ oa ∅).support, snd z ≤ qb := iff.rfl

@[simp] lemma is_query_bound_return (a : α) :
  is_query_bound (return a : oracle_comp spec α) qb :=
λ z hz, le_of_eq_of_le ((mem_support_simulate_return_iff _ _ _ z).1 hz).2 qb.empty_le

@[simp] lemma is_query_bound_query_iff (i : spec.ι) (t : spec.domain i) :
  is_query_bound (query i t) qb ↔ i ∈ qb.active_oracles :=
begin
  rw [is_query_bound_iff_forall],
  refine ⟨λ h, _, λ h z hz, _⟩,
  { specialize h (default, query_count.of_nat i 1) (by simp),
    simpa only [query_count.of_nat_le_iff, indexed_list.one_le_get_count_iff] using h },
  { rw [simulate_query, counting_oracle.apply_eq, query_count.increment_empty_eq_of_nat,
      support_map, support_query, set.image_univ, set.mem_range] at hz,
    obtain ⟨x, hx⟩ := hz,
    simpa [← hx] using h }
end

@[simp] lemma is_query_bound_bind_iff (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  is_query_bound (oa >>= ob) qb ↔ ∀ z ∈ (simulate countingₛₒ oa ∅).support,
    ∀ z' ∈ (simulate countingₛₒ (ob (fst z)) ∅).support, snd z + snd z' ≤ qb :=
begin
  rw [is_query_bound_iff_forall],
  refine ⟨λ h z hz z' hz', _, λ h, _⟩,
  {
    refine h (z'.1, z.2 + z'.2) _,
    rw [mem_support_simulate_bind_iff'],
    refine ⟨z, hz, _⟩,
    sorry,
  },
  {
    sorry,
  }
end

-- @[simp] lemma is_query_bound_bind_iff (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
--   is_query_bound (oa >>= ob) qb ↔
--     ∃ qb₁ qb₂, qb₁ + qb₂ ≤ qb ∧ is_query_bound oa qb₁ ∧ (∀ x, is_query_bound (ob x) qb₂) :=
-- begin
--   rw [is_query_bound_iff_forall],
--   refine ⟨_, λ h, _⟩,
--   {
--     intro h,
--     simp at h,
--   }
-- end

end oracle_comp