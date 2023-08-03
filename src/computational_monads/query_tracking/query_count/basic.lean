/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_comp
import algebra.big_operators.ring

/-!
# Structure for Counting Queries to Different Oracles

This file defines a simple `query_count` structure for tracking numbers of queries to oracles.
See `counting_oracle` for a way to generate a count during a simulation.

`query_bound` extends `query_count` to show that queries in a computation are actually bounded
by the count in the underlying `query_count`.

`query_log` and `query_store` extend a count to include a particular list rather than a count.
-/

namespace oracle_comp

open_locale big_operators
open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- A `query_count` represents a count of the number of queries made by a computation.
The count is non-zero for finitely many oracles as `oracle_comp` disallows unbounded recursion. -/
@[ext] structure query_count (spec : oracle_spec) :=
(get_count : spec.ι → ℕ)
(active_oracles : finset spec.ι)
(mem_active_oracles_iff' (i : spec.ι) : i ∈ active_oracles ↔ get_count i ≠ 0)

/-- View a `query_count` as a function from oracle index to a count. -/
instance query_count.fun_like (spec : oracle_spec) :
  fun_like (query_count spec) spec.ι (λ _, ℕ) :=
{ coe := query_count.get_count,
  coe_injective' := λ qc qc' h, query_count.ext qc qc' h
    (finset.ext (λ x, by simp_rw [query_count.mem_active_oracles_iff', h])) }

namespace query_count

variables (qc qc' : query_count spec)

@[simp] lemma get_count_eq_apply (i) : qc.get_count i = qc i := rfl

lemma mem_active_oracles_iff (i) : i ∈ qc.active_oracles ↔ qc i ≠ 0 :=
mem_active_oracles_iff' qc i

@[simp] lemma apply_eq_zero_iff (i) : qc i = 0 ↔ i ∉ qc.active_oracles :=
by simp [mem_active_oracles_iff]

lemma apply_ne_zero_iff (i) : qc i ≠ 0 ↔ i ∈ qc.active_oracles :=
(qc.mem_active_oracles_iff i).symm

@[simp] lemma apply_pos_iff (i) : 0 < qc i ↔ i ∈ qc.active_oracles :=
by simp [pos_iff_ne_zero]

lemma mem_active_oracles {i} (hi : qc i ≠ 0) : i ∈ qc.active_oracles :=
(mem_active_oracles_iff qc i).2 hi

lemma mem_active_oracles_of_lt {n i} (hi : n < qc i) : i ∈ qc.active_oracles :=
qc.mem_active_oracles (ne_zero_of_lt hi)

section empty

/-- The empty `query_count` has a count of zero for every oracle. -/
protected def empty (spec) : query_count spec :=
{ get_count := λ i, 0,
  active_oracles := ∅,
  mem_active_oracles_iff' := λ i, (ne_self_iff_false 0).symm }

instance : has_emptyc (query_count spec) := ⟨query_count.empty spec⟩
instance : inhabited (query_count spec) := ⟨∅⟩

@[simp] lemma empty_apply (i) : (∅ : query_count spec) i = 0 := rfl

@[simp] lemma active_oracles_empty : (∅ : query_count spec).active_oracles = ∅ := rfl

@[simp] lemma not_mem_active_oracles_empty (i) : i ∉ (∅ : query_count spec).active_oracles :=
finset.not_mem_empty i

end empty

section increment

/-- Increment the count in a `query_count` of the oracle at index `i` by `n`. -/
def increment (qc : query_count spec) (i : spec.ι) (n : ℕ) : query_count spec :=
{ get_count := λ i', if i = i' then qc i' + n else qc i',
  active_oracles := if n = 0 then qc.active_oracles else insert i qc.active_oracles,
  mem_active_oracles_iff' := nat.rec_on n (by simp)
    (by simp [ite_eq_iff, or_iff_not_imp_left, @eq_comm _ i]) }

lemma increment_apply (i n i') : (qc.increment i n) i' = if i = i' then qc i' + n else qc i' := rfl

@[simp] lemma increment_apply_self (i n) : (qc.increment i n) i = qc i + n := if_pos rfl

@[simp] lemma increment_apply_diff_index {i i'} (n) (h : i ≠ i') :
  (qc.increment i n) i' = qc i' := if_neg h

@[simp] lemma mem_active_oracles_increment_iff (i n i') :
  i' ∈ (qc.increment i n).active_oracles ↔
    (n ≠ 0 ∧ i' = i) ∨ i' ∈ qc.active_oracles :=
by induction n; simp [increment]

@[simp] lemma mem_active_oracles_increment_diff_index_iff {i i'} (n) (h : i ≠ i') :
  i' ∈ (qc.increment i n).active_oracles ↔ i' ∈ qc.active_oracles :=
by simp [h.symm]

@[simp] lemma increment_eq_self_iff (i n) : qc.increment i n = qc ↔ n = 0 :=
⟨λ h, by simpa using (fun_like.ext_iff.1 h) i,
  λ h, by simpa [fun_like.ext_iff, increment_apply] using h⟩

@[simp] lemma increment_zero (i) : qc.increment i 0 = qc := by simp

end increment

section decrement

def decrement (qc : query_count spec) (i : spec.ι) (n : ℕ) : query_count spec :=
{ get_count := λ i', if i = i' then qc i' - n else qc i',
  active_oracles := if qc i ≤ n then qc.active_oracles.erase i else qc.active_oracles,
  mem_active_oracles_iff' := λ i', begin
    split_ifs with hn hi hi,
    { simpa [hi] using hn },
    { simp [ne.symm hi] },
    { simp [qc.mem_active_oracles (ne_zero_of_lt (not_le.1 hn)), hn, ← hi] },
    { simp [hi] }
  end }

@[simp] lemma decrement_zero (i) : qc.decrement i 0 = qc :=
fun_like.ext _ _ (λ i', by simpa [decrement])

end decrement

section possible_outcomes

/-- Given a count of a number of queries to each oracle, get the number of possible outcomes,
assuming that each of the oracles could respond with any output. -/
def possible_outcomes (qc : query_count spec) : ℕ :=
∏ i in qc.active_oracles, (fintype.card (spec.range i)) ^ (qc i)

@[simp] lemma possible_outcomes_empty : possible_outcomes (∅ : query_count spec) = 1 := rfl

@[simp] lemma possible_outcomes_increment (i n) : possible_outcomes (qc.increment i n) =
  (possible_outcomes qc) * (fintype.card (spec.range i)) ^ n :=
begin
  induction n,
  { simp },
  { sorry }
end

@[simp] lemma possible_outcomes_decrement_of_le {i n} (h : n ≤ qc i) :
  possible_outcomes (qc.decrement i n) = (possible_outcomes qc) / (fintype.card (spec.range i)) ^ n :=
begin
  induction n,
  { simp },
  { sorry }
end

end possible_outcomes

end query_count

end oracle_comp