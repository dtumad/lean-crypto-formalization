/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_comp
import to_mathlib.general

/-!
# Structure for Counting Queries to Different Oracles

This file defines a simple `query_count` structure for tracking numbers of queries to oracles.
See `counting_oracle` for a way to generate a count during a simulation.

`query_bound` extends `query_count` to show that queries in a computation are actually bounded
by the count in the underlying `query_count`.

`query_log` and `query_store` extend a count to include a particular list rather than a count.
-/

namespace oracle_comp

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

lemma mem_active_oracles {i} (hi : qc i ≠ 0) : i ∈ qc.active_oracles :=
(mem_active_oracles_iff qc i).2 hi

@[simp] lemma apply_eq_zero_iff (i) : qc i = 0 ↔ i ∉ qc.active_oracles :=
by simp [mem_active_oracles_iff]

lemma apply_eq_zero {i} (hi : i ∉ qc.active_oracles) : qc i = 0 := (apply_eq_zero_iff qc i).2 hi

lemma apply_ne_zero_iff (i) : qc i ≠ 0 ↔ i ∈ qc.active_oracles :=
(qc.mem_active_oracles_iff i).symm

lemma apply_ne_zero {i} (hi : i ∈ qc.active_oracles) : qc i ≠ 0 := (apply_ne_zero_iff qc i).2 hi

@[simp] lemma apply_pos_iff (i) : 0 < qc i ↔ i ∈ qc.active_oracles :=
by simp [pos_iff_ne_zero]

lemma apply_pos {i} (hi : i ∈ qc.active_oracles) : 0 < qc i := (apply_pos_iff qc i).2 hi

lemma mem_active_oracles_of_lt {n i} (hi : n < qc i) : i ∈ qc.active_oracles :=
qc.mem_active_oracles (ne_zero_of_lt hi)

@[simp] lemma ite_apply (p : Prop) [decidable p] (i) :
  (if p then qc else qc') i = if p then qc i else qc' i :=
by split_ifs; refl

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

@[simp] lemma increment_apply (i n i') :
  (qc.increment i n) i' = if i = i' then qc i' + n else qc i' := rfl

lemma increment_apply_same_index {i i'} (n) (h : i = i') :
  (qc.increment i n) i' = qc i' + n := if_pos h

lemma increment_apply_diff_index {i i'} (n) (h : i ≠ i') :
  (qc.increment i n) i' = qc i' := if_neg h

lemma increment_apply_self (i n) : (qc.increment i n) i = qc i + n := if_pos rfl

lemma active_oracles_increment (i n) : (qc.increment i n).active_oracles =
  if n = 0 then qc.active_oracles else insert i qc.active_oracles := rfl

@[simp] lemma active_oracles_increment_succ (i n) : (qc.increment i (n + 1)).active_oracles =
  insert i qc.active_oracles := by simp [active_oracles_increment]

@[simp] lemma mem_active_oracles_increment_iff (i n i') :
  i' ∈ (qc.increment i n).active_oracles ↔ (n ≠ 0 ∧ i = i') ∨ i' ∈ qc.active_oracles :=
by induction n; simp [increment, @eq_comm _ i]

lemma mem_active_oracles_increment_same_index_iff {i i'} (n) (h : i = i') :
  i' ∈ (qc.increment i n).active_oracles ↔ n ≠ 0 ∨ i' ∈ qc.active_oracles := by simp [h]

lemma mem_active_oracles_increment_diff_index_iff {i i'} (n) (h : i ≠ i') :
  i' ∈ (qc.increment i n).active_oracles ↔ i' ∈ qc.active_oracles := by simp [h]

lemma mem_active_oracles_increment_self_iff (i n) :
  i ∈ (qc.increment i n).active_oracles ↔ n ≠ 0 ∨ i ∈ qc.active_oracles := by simp

@[simp] lemma increment_increment (i n m) :
  (qc.increment i n).increment i m = qc.increment i (n + m) :=
fun_like.ext _ _ (λ i', by by_cases hi : i = i'; simp [hi, add_assoc])

@[simp] lemma increment_eq_self_iff (i n) : qc.increment i n = qc ↔ n = 0 :=
⟨λ h, by simpa using (fun_like.ext_iff.1 h) i,
  λ h, by simpa [fun_like.ext_iff, increment_apply] using h⟩

@[simp] lemma increment_zero (i) : qc.increment i 0 = qc := by simp

end increment

section of_nat

/-- Create a `query_count` from a single entry at index `i`. -/
def of_nat (i : spec.ι) (n : ℕ) : query_count spec :=
query_count.increment ∅ i n

@[simp] lemma of_nat_apply (i : spec.ι) (n i') :
  (of_nat i n) i' = if i = i' then n else 0 := by simp [of_nat]

lemma of_nat_apply_same_index {i i' : spec.ι} (n) (h : i = i') : (of_nat i n) i' = n := by simp [h]

lemma of_nat_apply_diff_index {i i' : spec.ι} (n) (h : i ≠ i') : (of_nat i n) i' = 0 := by simp [h]

lemma of_nat_apply_self (i : spec.ι) (n) : (of_nat i n) i = n := by simp

lemma active_oracles_of_nat (i : spec.ι) (n) : (of_nat i n).active_oracles =
  if n = 0 then ∅ else {i} := by simp [of_nat, active_oracles_increment]

@[simp] lemma mem_active_oracles_of_nat_iff (i : spec.ι) (n i') :
  i' ∈ (of_nat i n).active_oracles ↔ n ≠ 0 ∧ i = i' := by simp [of_nat]

@[simp] lemma increment_of_nat (i : spec.ι) (n m) :
  (of_nat i n).increment i m = of_nat i (n + m) := increment_increment ∅ i n m

@[simp] lemma of_nat_eq_empty_iff (i : spec.ι) (n) : of_nat i n = ∅ ↔ n = 0 := by simp [of_nat]

@[simp] lemma of_nat_zero (i : spec.ι) : of_nat i 0 = ∅ := by simp

end of_nat

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

@[simp] lemma decrement_apply (i n i') : (qc.decrement i n) i' =
  if i = i' then qc i' - n else qc i' := rfl

lemma decrement_apply_same_index {i i'} (n) (h : i = i') :
  (qc.decrement i n) i' = qc i' - n := if_pos h

lemma decrement_apply_diff_index {i i'} (n) (h : i ≠ i') :
  (qc.decrement i n) i' = qc i' := if_neg h

lemma decrement_apply_self (i n) : (qc.decrement i n) i = qc i - n := if_pos rfl

lemma active_oracles_decrement (i n) : (qc.decrement i n).active_oracles =
  if qc i ≤ n then qc.active_oracles.erase i else qc.active_oracles := rfl

@[simp] lemma mem_active_oracles_decrement_iff (i n i') :
  i' ∈ (qc.decrement i n).active_oracles ↔ (n < qc i ∨ i ≠ i') ∧ i' ∈ qc.active_oracles :=
by by_cases hn : qc i ≤ n; simp [hn, active_oracles_decrement, @eq_comm _ i, lt_iff_not_le]

lemma mem_active_oracles_decrement_same_index_iff {i i'} (n) (h : i = i') :
  i' ∈ (qc.decrement i n).active_oracles ↔ n < qc i ∧ i ∈ qc.active_oracles := by simp [h]

lemma mem_active_oracles_decrement_diff_index_iff {i i'} (n) (h : i ≠ i') :
  i' ∈ (qc.decrement i n).active_oracles ↔ i' ∈ qc.active_oracles := by simp [h]

lemma mem_active_oracles_decrement_self_iff (i n) :
  i ∈ (qc.decrement i n).active_oracles ↔ n < qc i ∧ i ∈ qc.active_oracles := by simp

@[simp] lemma decrement_decrement (i n m) :
  (qc.decrement i n).decrement i m = qc.decrement i (n + m) :=
fun_like.ext _ _ (λ i', by by_cases hi : i = i'; simp [hi, nat.sub_sub])

@[simp] lemma decrement_eq_self_iff (i n) : qc.decrement i n = qc ↔ n = 0 ∨ qc i = 0 :=
begin
  refine ⟨λ h, _, λ h, by cases h with h h; simp [fun_like.ext_iff, h]⟩,
  have := (fun_like.ext_iff.1 h) i,
  simp only [decrement_apply, eq_self_iff_true, if_true] at this,
  cases n with n,
  { exact or.inl rfl },
  { cases (qc i) with m,
    { exact or.inr rfl },
    { rw [nat.succ_sub_succ] at this,
      exact ((this.symm ▸ not_le_of_lt (nat.lt_succ_self m) : ¬ m - n ≤ m) tsub_le_self).elim } }
end

@[simp] lemma decrement_zero (i) : qc.decrement i 0 = qc :=
fun_like.ext _ _ (λ i', by simpa [decrement])

end decrement

lemma decrement_increment_eq_increment (i) {n m} (hnm : m ≤ n) :
  (qc.increment i n).decrement i m = qc.increment i (n - m) :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [nat.add_sub_assoc hnm] },
  { simp [hi] }
end

lemma decrement_increment_eq_decrement (i) {n m} (hnm : n ≤ m) :
  (qc.increment i n).decrement i m = qc.decrement i (m - n) :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [nat_helper_thing hnm] },
  { simp [hi] }
end

lemma increment_decrement_eq_increment (i) {n m} (hm : m ≤ qc i) (hnm : m ≤ n) :
  (qc.decrement i m).increment i n = qc.increment i (n - m) :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [← nat.sub_add_comm hm, nat.add_sub_assoc hnm] },
  { simp [hi] }
end

lemma increment_decrement_eq_decrement (i) {n m} (hm : m ≤ qc i) (hnm : n ≤ m) :
  (qc.decrement i m).increment i n = qc.decrement i (m - n) :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [← nat.sub_add_comm hm, nat_helper_thing hnm] },
  { simp [hi] }
end

lemma increment_decrement_comm (i) {n m} (hm : m ≤ qc i) (hnm : m ≤ n) :
  (qc.increment i n).decrement i m = (qc.decrement i m).increment i n :=
by rw [decrement_increment_eq_increment qc i hnm, increment_decrement_eq_increment qc i hm hnm]

@[simp] lemma decrement_increment_eq_self (i n) : (qc.increment i n).decrement i n = qc :=
by simp [decrement_increment_eq_increment qc i le_rfl]

lemma increment_decrement_eq_self (i n) (hm : n ≤ qc i) :
  (qc.decrement i n).increment i n = qc :=
by simp [increment_decrement_eq_increment qc i hm le_rfl]

section reset_count

/-- Reset the count at index `i` to `n`, unless the current count is below the new value.
This aligns with the behavior of a function like `list.take` that doesn't add new values. -/
def reset_count (qc : query_count spec) (i : spec.ι) (n : ℕ) : query_count spec :=
(qc.decrement i (qc i)).increment i (min n (qc i))

@[simp] lemma reset_count_apply (i n i') : (qc.reset_count i n) i' =
  if i = i' then min n (qc i') else qc i' :=
begin
  by_cases hi : i = i',
  { induction hi,
    simp [reset_count] },
  { simp [reset_count, hi] }
end

@[simp] lemma active_oracles_reset_count (i n) : (qc.reset_count i n).active_oracles =
  if n = 0 then qc.active_oracles.erase i else qc.active_oracles :=
begin
  refine finset.ext (λ i', _),
  cases n,
  { simp [reset_count, @eq_comm _ i] },
  { by_cases hi : i = i',
    { induction hi,
      simp [reset_count] },
    { simp [hi, reset_count] } }
end

@[simp] lemma reset_count_eq_self (i) : qc.reset_count i (qc i) = qc :=
by simp [reset_count, increment_decrement_eq_self qc i (qc i) le_rfl]

@[simp] lemma reset_count_zero (i) : qc.reset_count i 0 = qc.decrement i (qc i) :=
by simp [reset_count]

end reset_count

end query_count

end oracle_comp