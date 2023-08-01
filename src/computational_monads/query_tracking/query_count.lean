/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_comp

/-!
# Structure for Counting Queries to Different Oracles

This file defines a simple `query_count` structure for tracking numbers of queries to oracles.
See `counting_oracle` for a way to generate a count during a simulation.

`query_bound` extends `query_count` to show that queries in a computation are actually bounded
by the count in the underlying `query_count`.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- A `query_count` represents a count of the number of queries made by a computation.
The count is non-zero for finitely many oracles as `oracle_comp` disallows unbounded recursion. -/
structure query_count (spec : oracle_spec) :=
(get_count : spec.ι → ℕ)
(active_oracles : finset spec.ι)
(mem_active_oracles_iff (i : spec.ι) : i ∈ active_oracles ↔ get_count i ≠ 0)

variables (qc qc' : query_count spec)

namespace query_count

@[simp] lemma get_count_eq_zero_iff (i) : qc.get_count i = 0 ↔ i ∉ qc.active_oracles :=
by simp [mem_active_oracles_iff]

lemma get_count_ne_zero_iff (i) : qc.get_count i ≠ 0 ↔ i ∈ qc.active_oracles :=
(qc.mem_active_oracles_iff i).symm

@[simp] lemma get_count_pos_iff (i) : 0 < qc.get_count i ↔ i ∈ qc.active_oracles :=
by simp [pos_iff_ne_zero]

section empty

/-- The empty `query_count` has a count of zero for every oracle. -/
@[simps] protected def empty (spec) : query_count spec :=
{ get_count := λ i, 0,
  active_oracles := ∅,
  mem_active_oracles_iff := λ i, (ne_self_iff_false 0).symm }

instance : has_emptyc (query_count spec) := ⟨query_count.empty spec⟩
instance : inhabited (query_count spec) := ⟨∅⟩

lemma not_mem_active_oracles_empty (i) : i ∉ (∅ : query_count spec).active_oracles :=
finset.not_mem_empty i

end empty

section count_query

def count_query (qc : query_count spec) (i : spec.ι) : query_count spec :=
{ get_count := λ i', if i = i' then qc.get_count i' + 1 else qc.get_count i',
  active_oracles := insert i qc.active_oracles,
  mem_active_oracles_iff := by simp [ite_eq_iff, or_iff_not_imp_left, @eq_comm _ i] }

lemma get_count_count_query (i i') : (qc.count_query i).get_count i' =
  if i = i' then qc.get_count i' + 1 else qc.get_count i' := rfl

@[simp] lemma get_count_count_query_same_index (i) :
  (qc.count_query i).get_count i = qc.get_count i + 1 := if_pos rfl

@[simp] lemma get_count_count_query_diff_index {i i'} (h : i ≠ i') :
  (qc.count_query i).get_count i' = qc.get_count i' := if_neg h

@[simp] lemma mem_active_oracles_count_query_iff (i i') :
  i' ∈ (qc.count_query i).active_oracles ↔ i' = i ∨ i' ∈ qc.active_oracles := finset.mem_insert

lemma mem_active_oracles_count_query_same_index (i) : i ∈ (qc.count_query i).active_oracles :=
(mem_active_oracles_count_query_iff qc i i).2 (or.inl rfl)

@[simp] lemma mem_active_oracles_count_query_diff_index {i i'} (h : i ≠ i') :
  i' ∈ (qc.count_query i).active_oracles ↔ i' ∈ qc.active_oracles :=
by simp [h.symm]

end count_query

end query_count

end oracle_comp