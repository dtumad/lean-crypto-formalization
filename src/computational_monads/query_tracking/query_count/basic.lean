/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.indexed_list.order
import to_mathlib.general

/-!
# Structure for Counting Queries to Different Oracles

This file defines a simple `query_count` structure for tracking numbers of queries to oracles.
See `counting_oracle` for a way to generate a count during a simulation.

`queries_at_most` uses `query_count` to show that queries in a computation are actually bounded
by the count in the underlying `query_count`.

`query_log` and `query_store` extend a count to include a particular list rather than a count.
-/

namespace oracle_spec

open_locale big_operators
open indexed_list

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- A `query_count` represents a count of the number of queries made by a computation.
The count is non-zero for finitely many oracles as `oracle_comp` disallows unbounded recursion. -/
@[inline, reducible] def query_count (spec : oracle_spec) :=
spec.indexed_list (λ _, unit)

namespace query_count

lemma apply_eq_replicate_get_count (qc : spec.query_count) (i) :
  qc i = list.replicate (qc.get_count i) () :=
begin
  rw [get_count_eq_length_apply],
  induction qc i with t ts hts,
  { refl },
  { rw [list.length_cons, list.replicate_succ, hts, list.length_replicate, subsingleton.elim t] }
end

protected lemma get_count_ext (qc qc' : spec.query_count)
  (h : ∀ i, qc.get_count i = qc'.get_count i) : qc = qc' :=
fun_like.ext _ _ (λ i, by simp_rw [apply_eq_replicate_get_count, h i])

protected lemma get_count_ext_iff {qc qc' : spec.query_count} :
  qc = qc' ↔ ∀ i, qc.get_count i = qc'.get_count i :=
⟨λ h i, congr_arg _ h, query_count.get_count_ext qc qc'⟩

variables (qc qc' qc'' : spec.query_count)

instance : add_cancel_comm_monoid (spec.query_count) :=
{ add_comm := λ il il', query_count.get_count_ext _ _
    (λ i, by rw [get_count_add, get_count_add, add_comm]),
  .. indexed_list.add_cancel_monoid }

section sub

def sub (qc qc' : spec.query_count) : spec.query_count :=
{ to_fun := λ i, (qc i).drop (qc'.get_count i),
  active_oracles := qc.active_oracles.filter (λ i, qc'.get_count i < qc.get_count i),
  mem_active_oracles_iff' := λ i, begin
    rw [ne.def, list.drop_eq_nil_iff_le, finset.mem_filter, not_le, ← get_count_pos_iff],
    exact ⟨λ h, h.2, λ h, ⟨lt_of_le_of_lt zero_le' h, h⟩⟩,
  end }

/-- Subtraction operation on `query_count` given by removing elements from the first lists
equal to the number of elements in the second list, for each index. -/
instance : has_sub (spec.query_count) := { sub := sub }

@[simp] lemma sub_apply (i) : (qc - qc') i = (qc i).drop (qc'.get_count i) := rfl

@[simp] lemma active_oracles_sub : (qc - qc').active_oracles =
  qc.active_oracles.filter (λ i, qc'.get_count i < qc.get_count i) := rfl

@[simp] lemma get_count_sub (i) : (qc - qc').get_count i = qc.get_count i - qc'.get_count i :=
by simp [get_count_eq_length_apply]

@[simp] protected lemma sub_sub : qc - qc' - qc'' = qc - (qc' + qc'') :=
query_count.get_count_ext _ _ (λ i, by simp [nat.sub_sub])

@[simp] lemma sub_empty : qc - ∅ = qc := by simp [fun_like.ext_iff]

end sub

section of_nat

def of_nat (i : spec.ι) (n : ℕ) : spec.query_count :=
@of_list _ _ i (list.replicate n ())

variables (i : spec.ι) (n m : ℕ)

@[simp] lemma of_nat_apply (i') : of_nat i n i' = if i = i' then list.replicate n () else [] :=
by simp only [of_nat, of_list_apply, dif_eq_if, eq_rec_constant]

@[simp] lemma active_oracles_of_nat : (of_nat i n).active_oracles = if n = 0 then ∅ else {i} :=
by simp [of_nat, list.empty_iff_eq_nil, list.eq_nil_iff_forall_not_mem, list.mem_replicate]

@[simp] lemma get_count_of_nat (i') : (of_nat i n).get_count i' = if i = i' then n else 0 :=
by simp [of_nat]

lemma get_count_of_nat_self : (of_nat i n).get_count i = n :=
by simp only [get_count_of_nat, eq_self_iff_true, if_true]

@[simp] lemma of_nat_zero : of_nat i 0 = ∅ := by simp [fun_like.ext_iff]

lemma of_nat_add : of_nat i (n + m) = of_nat i n + of_nat i m :=
fun_like.ext _ _ (λ i', by by_cases hi : i = i'; simp [hi, list.replicate_add])

lemma of_list_eq_of_nat_length (ts : list unit) : @of_list _ _ i ts = of_nat i ts.length :=
begin
  induction ts with t ts hts,
  { simp },
  { rw [list.length_cons, of_nat_add, ← hts, of_nat, add_comm, ← of_list_append,
      list.replicate_one, subsingleton.elim t unit.star, list.singleton_append] }
end

@[simp] lemma nsmul_of_nat : n • (of_nat i m) = of_nat i (n * m) :=
begin
  induction n with n hn,
  { rw [zero_nsmul, zero_mul, of_nat_zero, zero_eq_empty] },
  { rw [succ_nsmul, hn, nat.succ_mul, of_nat_add, add_comm] }
end

end of_nat

/-- We can express a `query_count` as a sum over the active indices of the list
of the individiaul counts for each index. Doesn't work with an arbitrary `indexed_list`
since the addition operation there isn't commutative. -/
lemma sum_of_nat_get_count : ∑ i in qc.active_oracles, of_nat i (qc.get_count i) = qc :=
begin
  refine @add_values_induction _ _ (λ qc, ∑ i in qc.active_oracles, of_nat i (qc.get_count i) = qc)
    qc (by rw [active_oracles_empty, finset.sum_empty, zero_eq_empty]) (λ i ts il hts hil h, _),
  have : ts ≠ [] := hts,
  simp [list.empty_iff_eq_nil, this, of_nat_add, finset.sum_add_distrib] at h ⊢,
  rw [add_values, finset.sum_insert hil, h, get_count_eq_zero il hil, of_nat_zero, empty_add],
  refine congr_arg (λ il', il + il') _,
  refine trans (finset.sum_eq_single_of_mem i (finset.mem_insert_self _ _) (λ i' hi' hi'',
    by simp [ne.symm hi'', zero_eq_empty])) (by simp [of_list_eq_of_nat_length]),
end

section increment

/-- Increment the count in a `query_count` of the oracle at index `i` by `n`. -/
def increment (qc : spec.query_count) (i : spec.ι) (n : ℕ) :
  spec.query_count := qc + of_nat i n

lemma increment_eq_of_nat_add (i n) : qc.increment i n = of_nat i n + qc := add_comm _ _
lemma increment_eq_add_of_nat (i n) : qc.increment i n = qc + of_nat i n := rfl

@[simp] lemma increment_apply (i n i') : qc.increment i n i' =
  if i = i' then qc i' ++ list.replicate n () else qc i' :=
by by_cases hi : i = i'; simp [hi, increment, add_apply, of_nat_apply]

@[simp] lemma active_oracles_increment (i n) : (qc.increment i n).active_oracles =
  if n = 0 then qc.active_oracles else insert i qc.active_oracles :=
finset.ext (λ i', by by_cases hn : n = 0; simp [hn, increment, or_comm])

@[simp] lemma get_count_increment (i n i') : (qc.increment i n).get_count i' =
  qc.get_count i' + if i = i' then n else 0 := by simp [increment]

lemma get_count_increment_self (i n) : (qc.increment i n).get_count i = qc.get_count i + n :=
by simp only [get_count_increment, eq_self_iff_true, if_true]

lemma mem_active_oracles_increment_iff (i n i') :
  i' ∈ (qc.increment i n).active_oracles ↔ (n ≠ 0 ∧ i = i') ∨ i' ∈ qc.active_oracles :=
by induction n with n hn; simp [@eq_comm _ i]

lemma mem_active_oracles_increment_same_index_iff {i i'} (n) (h : i = i') :
  i' ∈ (qc.increment i n).active_oracles ↔ n ≠ 0 ∨ i' ∈ qc.active_oracles :=
by simp [h, -active_oracles_increment, mem_active_oracles_increment_iff]

lemma mem_active_oracles_increment_diff_index_iff {i i'} (n) (h : i ≠ i') :
  i' ∈ (qc.increment i n).active_oracles ↔ i' ∈ qc.active_oracles :=
by simp [h, -active_oracles_increment, mem_active_oracles_increment_iff]

lemma mem_active_oracles_increment_self_iff (i n) :
  i ∈ (qc.increment i n).active_oracles ↔ n ≠ 0 ∨ i ∈ qc.active_oracles :=
by simp [-active_oracles_increment, mem_active_oracles_increment_iff]

@[simp] lemma increment_eq_self_iff (i n) : qc.increment i n = qc ↔ n = 0 :=
⟨λ h, by simpa using congr_arg (λ il, get_count il i) h,
  λ h, query_count.get_count_ext _ _ (λ i', by rw [get_count_increment, h, if_t_t, add_zero])⟩

@[simp] lemma increment_zero (i) : qc.increment i 0 = qc := by simp only [increment_eq_self_iff]

@[simp] lemma increment_increment (i n m) :
  (qc.increment i n).increment i m = qc.increment i (n + m) :=
by simp [increment, of_nat_add, add_assoc]

@[simp] lemma add_values_eq_increment (i) (ts : list unit) :
  @add_values _ _ i qc ts = qc.increment i ts.length :=
by rw [increment, add_values, of_list_eq_of_nat_length]

lemma increment_add (i n) : qc.increment i n + qc' = (qc + qc').increment i n :=
by rw [increment, add_comm _ qc', ← add_assoc, increment, add_comm qc']

lemma add_increment (i n) : qc + qc'.increment i n = (qc + qc').increment i n :=
by rw [add_comm qc, increment_add, add_comm qc]

@[simp] lemma increment_empty_eq_of_nat (i n) :
  (∅ : spec.query_count).increment i n = of_nat i n :=
by rw [increment_eq_of_nat_add, add_empty]

lemma increment_succ (i n) : qc.increment i (n + 1) = qc.increment i n + of_nat i 1 :=
by rw [increment_eq_add_of_nat, of_nat_add, ← add_assoc, ← increment_eq_add_of_nat qc]

lemma increment_increment_comm (i j n m) :
  (qc.increment i n).increment j m = (qc.increment j m).increment i n :=
by simp_rw [increment_eq_of_nat_add, ← add_assoc, add_comm (of_nat j m)]

lemma increment_add_eq_add_increment (i n) :
  (qc + qc').increment i n = qc + qc'.increment i n :=
begin
  refine fun_like.ext_iff.2 (λ j, _),
  by_cases hj : i = j,
  { simp only [hj, increment_apply, eq_self_iff_true, add_apply, list.append_assoc, if_true] },
  { simp only [hj, increment_apply, add_apply, if_false] }
end

lemma increment_add_eq_increment_add (i n) :
  (qc + qc').increment i n = qc.increment i n + qc' :=
by rw [add_comm qc qc', increment_add_eq_add_increment, add_comm qc']

@[simp] lemma nmsul_increment (i m) (n : ℕ) :
  n • (qc.increment i m) = (n • qc).increment i (n * m) :=
by simp [increment_eq_add_of_nat]

end increment

section decrement

def decrement (qc : spec.query_count) (i : spec.ι) (n : ℕ) :
  spec.query_count := qc - of_nat i n

lemma decrement_eq_sub_of_nat (i n) : qc.decrement i n = qc - of_nat i n := rfl

@[simp] lemma decrement_apply (i n i') : qc.decrement i n i' =
  if i = i' then (qc i').drop n else qc i' :=
by by_cases hi : i = i'; simp [hi, decrement]

@[simp] lemma active_oracles_decrement (i n) : (qc.decrement i n).active_oracles =
  if qc.get_count i ≤ n then qc.active_oracles.erase i else qc.active_oracles :=
begin
  refine finset.ext (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    by_cases hn : qc.get_count i ≤ n; simp [hn, decrement, ← not_le] },
  { by_cases hn : get_count qc i ≤ n; simp [hn, hi, ne.symm hi, decrement] }
end

@[simp] lemma get_count_decrement (i n i') : (qc.decrement i n).get_count i' =
  qc.get_count i' - if i = i' then n else 0 := by simp [decrement]

lemma mem_active_oracles_decrement_iff (i n i') : i' ∈ (qc.decrement i n).active_oracles ↔
  (n < qc.get_count i ∨ i ≠ i') ∧ i' ∈ qc.active_oracles :=
by by_cases hn : qc.get_count i ≤ n; simp [hn, active_oracles_decrement,
  @eq_comm _ i, lt_iff_not_le]

lemma mem_active_oracles_decrement_same_index_iff {i i'} (n) (h : i = i') :
  i' ∈ (qc.decrement i n).active_oracles ↔ n < qc.get_count i ∧ i ∈ qc.active_oracles :=
by simp [h, -active_oracles_decrement, mem_active_oracles_decrement_iff]

lemma mem_active_oracles_decrement_diff_index_iff {i i'} (n) (h : i ≠ i') :
  i' ∈ (qc.decrement i n).active_oracles ↔ i' ∈ qc.active_oracles :=
by simp [h, -active_oracles_decrement, mem_active_oracles_decrement_iff]

lemma mem_active_oracles_decrement_self_iff (i n) :
  i ∈ (qc.decrement i n).active_oracles ↔ n < qc.get_count i ∧ i ∈ qc.active_oracles :=
by simp [-active_oracles_decrement, mem_active_oracles_decrement_iff]

@[simp] lemma decrement_empty (i n) : (∅ : spec.query_count).decrement i n = ∅ := by simp

@[simp] lemma decrement_zero (i) : qc.decrement i 0 = qc := by simp [decrement]

@[simp] lemma decrement_add (i n m) :
  qc.decrement i (n + m) = (qc.decrement i n).decrement i m :=
by simp [decrement, query_count.sub_sub, of_nat_add]

lemma decrement_add_eq_add_decrement (i n) :
  (qc + qc').decrement i n = qc.decrement i n + qc'.decrement i (n - qc.get_count i) :=
begin
  refine fun_like.ext_iff.2 (λ j, _),
  by_cases hj : i = j,
  { simp only [hj, list.drop_append_eq_append_drop, get_count_eq_length_apply, decrement_apply,
      eq_self_iff_true, add_apply, if_true] },
  { simp only [hj, decrement_apply, add_apply, if_false] }
end

end decrement

lemma decrement_increment_eq_increment (i) {n m} (hnm : m ≤ n) :
  (qc.increment i n).decrement i m = qc.increment i (n - m) :=
begin
  refine query_count.get_count_ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [nat.add_sub_assoc hnm] },
  { simp [hi] }
end

lemma decrement_increment_eq_decrement (i) {n m} (hnm : n ≤ m) :
  (qc.increment i n).decrement i m = qc.decrement i (m - n) :=
begin
  refine query_count.get_count_ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [nat_helper_thing hnm] },
  { simp [hi] }
end

lemma increment_decrement_eq_increment (i) {n m} (hm : m ≤ qc.get_count i) (hnm : m ≤ n) :
  (qc.decrement i m).increment i n = qc.increment i (n - m) :=
begin
  refine query_count.get_count_ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [← nat.sub_add_comm hm, nat.add_sub_assoc hnm] },
  { simp [hi] }
end

lemma increment_decrement_eq_decrement (i) {n m} (hm : m ≤ qc.get_count i) (hnm : n ≤ m) :
  (qc.decrement i m).increment i n = qc.decrement i (m - n) :=
begin
  refine query_count.get_count_ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [← nat.sub_add_comm hm, nat_helper_thing hnm] },
  { simp [hi] }
end

lemma increment_decrement_comm (i) {n m} (hm : m ≤ qc.get_count i) (hnm : m ≤ n) :
  (qc.increment i n).decrement i m = (qc.decrement i m).increment i n :=
by rw [decrement_increment_eq_increment qc i hnm, increment_decrement_eq_increment qc i hm hnm]

@[simp] lemma decrement_increment_eq_self (i n) : (qc.increment i n).decrement i n = qc :=
by simp [decrement_increment_eq_increment qc i le_rfl]

lemma increment_decrement_eq_self (i n) (hm : n ≤ qc.get_count i) :
  (qc.decrement i n).increment i n = qc :=
by simp [increment_decrement_eq_increment qc i hm le_rfl]

@[simp] lemma increment_decrement_eq_self_iff (i n m) :
  (qc.decrement i n).increment i m = qc ↔ m = min (qc.get_count i) n :=
begin
  refine query_count.get_count_ext_iff.trans ⟨λ h, _, λ h j, _⟩,
  { specialize h i,
    simp only [get_count_increment, get_count_decrement, eq_self_iff_true, if_true] at h,
    rw [eq_comm, min_eq_iff, get_count_eq_length_apply],
    by_cases hn : n ≤ qc.get_count i,
    { rw [← nat.sub_add_comm hn, nat.sub_eq_iff_eq_add (le_trans hn (le_add_right le_rfl))] at h,
      exact or.inr ⟨(add_left_cancel h).symm, hn⟩ },
    { rw [nat.sub_eq_zero_of_le (le_of_not_le hn), zero_add] at h,
      refine or.inl ⟨h.symm, le_of_not_le hn⟩ } },
  { by_cases hj : i = j,
    { induction hj,
      simp only [get_count_increment, get_count_decrement, eq_self_iff_true, if_true],
      rw [h, nat.sub_add_min_cancel] },
    { simp only [hj, get_count_increment, get_count_decrement, if_false, tsub_zero, add_zero] } }
end

/-- Simplified version of `indexed_list.add_values_induction` for the case of `query_count`.
Makes use of `increment` and simplifies some assumptions from lists to integers. -/
lemma increment_induction {p : spec.query_count → Prop} (qc : spec.query_count)
  (h₁ : p ∅) (h₂ : ∀ ⦃i : spec.ι⦄ (n : ℕ) (qc : spec.query_count),
    i ∉ qc.active_oracles → p qc → p (qc.increment i n.succ)) : p qc :=
begin
  refine qc.add_values_induction h₁ (λ i ts qc hqc h hp, _),
  have : p (increment qc i ts.length),
  from nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil hqc) ▸ h₂ ts.length.pred qc h hp,
  exact (add_values_eq_increment qc i ts).symm ▸ this
end

section sums

lemma get_count_sum (s : finset α) (qc : α → spec.query_count) (j : spec.ι) :
  (∑ i in s, qc i).get_count j = ∑ i in s, (qc i).get_count j :=
begin
  refine finset.cons_induction _ (λ i s hs h, _) s,
  { rw [finset.sum_empty, finset.sum_empty, get_count_zero] },
  { rw [finset.sum_cons hs, finset.sum_cons hs, get_count_add, h] }
end

lemma eq_sum_active_oracles_of_nat_get_count (qc : spec.query_count) :
  qc = ∑ i in qc.active_oracles, of_nat i (qc.get_count i) :=
begin
  refine query_count.get_count_ext _ _ (λ i, _),
  simp_rw [get_count_sum, get_count_of_nat, finset.sum_ite_eq'],
  split_ifs with hi; simp [hi]
end

end sums

section reduce

def reduce (qc : spec.query_count) (f : spec.ι → spec'.ι) : spec'.query_count :=
∑ i in qc.active_oracles, of_nat (f i) (qc.get_count i)

end reduce

section transform

@[simp] lemma list.replicate_eq_nil {α : Type} (x : α) (n : ℕ) :
  list.replicate n x = [] ↔ n = 0 := by cases n; simp

def transform (qc : spec.query_count)
  (s : spec.ι → spec'.query_count) : spec'.query_count :=
{ to_fun := λ j, let k := ∑ i in qc.active_oracles, qc.get_count i * ((s i).get_count j) in
    list.replicate k (),
  active_oracles := qc.active_oracles.bUnion (λ i, (s i).active_oracles),
  mem_active_oracles_iff' := by simp [not_or_distrib] }

variables (s : spec.ι → spec'.query_count)

@[simp] lemma transform_apply (j : spec'.ι) : qc.transform s j =
  list.replicate (∑ i in qc.active_oracles, qc.get_count i * ((s i).get_count j)) () := rfl

@[simp] lemma active_oracles_transform : (qc.transform s).active_oracles =
  qc.active_oracles.bUnion (λ i, (s i).active_oracles) := rfl

@[simp] lemma get_count_transform (j : spec'.ι) : (qc.transform s).get_count j =
  ∑ i in qc.active_oracles, qc.get_count i * ((s i).get_count j) :=
by simp [get_count_eq_length_apply]

@[simp] lemma transform_empty : transform ∅ s = ∅ := by simp

@[simp] lemma transform_of_nat (i : spec.ι) (n : ℕ) :
  (of_nat i n).transform s = n • s i :=
begin
  cases n with n,
  { simp [zero_eq_empty] },
  { simp [query_count.get_count_ext_iff] },
end

@[simp] lemma transform_add : (qc + qc').transform s = qc.transform s + qc'.transform s :=
begin
  simp [query_count.get_count_ext_iff, add_mul],
  refine λ i, finset.sum_add_distrib.trans _,
  congr' 1,
  { refine symm (finset.sum_subset (finset.subset_union_left _ _) _),
    simp [imp_or_distrib] },
  { refine symm (finset.sum_subset (finset.subset_union_right _ _) _),
    simp [imp_or_distrib] }
end

-- @[simp] lemma transform_sub : (qc - qc').transform s = qc.transform s - qc'.transform s :=
-- begin
--   simp [query_count.get_count_ext_iff, tsub_mul],
--   refine λ i, finset.sum_sub_distrib.trans _,
-- end

@[simp] lemma transform_increment (i : spec.ι) (n : ℕ) :
  transform (qc.increment i n) s = qc.transform s + n • s i :=
by simp [increment_eq_add_of_nat]

-- @[simp] lemma transform_decrement (i : spec.ι) (n : ℕ) :
--   transform (qc.decrement i n) s = qc.transform s - n • s i :=
-- by simp [increment_eq_sub_of_nat]

end transform

end query_count

namespace indexed_list

open query_count

variables {τ τ' : spec.ι → Type}

section to_query_count

/-- View any `indexed_list` as a `query_count` by replacing all values with `()`. -/
def to_query_count (il : spec.indexed_list τ) : spec.query_count :=
il.map (λ _ _, ())

variables (il il' : spec.indexed_list τ)

@[simp] lemma apply_to_query_count (i) :
  il.to_query_count i = list.replicate (il.get_count i) () := list.map_const _ _

@[simp] lemma active_oracles_to_query_count :
  il.to_query_count.active_oracles = il.active_oracles := rfl

@[simp] lemma get_count_to_query_count : il.to_query_count.get_count = il.get_count :=
by simp [to_query_count]

@[simp] lemma to_query_count_empty : (∅ : spec.indexed_list τ).to_query_count = ∅ := map_empty _

lemma to_query_count_eq_empty_iff : il.to_query_count = ∅ ↔ il = ∅ :=
by simp only [eq_empty_iff, active_oracles_to_query_count]

@[simp] lemma to_query_count_add : (il + il').to_query_count =
  il.to_query_count + il'.to_query_count := map_add _ _ _

@[simp] lemma to_query_count_of_list {i} (ts : list (τ i)) :
  (of_list ts).to_query_count = of_nat i ts.length :=
by simp [to_query_count, of_nat]

@[simp] lemma to_query_count_add_values {i} (ts : list (τ i)) :
  (il.add_values ts).to_query_count = increment il.to_query_count i ts.length :=
by simp [add_values, increment]

@[simp] lemma to_query_count_take_at_index (i n) : (il.take_at_index i n).to_query_count =
  take_at_index il.to_query_count i n := map_take_at_index _ _ _ _

@[simp] lemma to_query_count_drop_at_index (i n) : (il.drop_at_index i n).to_query_count =
  drop_at_index il.to_query_count i n := map_drop_at_index _ _ _ _

lemma to_query_count_eq_add_iff (qc qc' : spec.query_count) : il.to_query_count = qc + qc' ↔
  ∃ il₁ il₂, il₁ + il₂ = il ∧ il₁.to_query_count = qc ∧ il₂.to_query_count = qc' :=
begin
  refine ⟨_, λ h, _⟩,
  { revert qc qc',
    refine add_values_induction il _ _,
    { simp only [to_query_count_empty, empty_eq_add, add_eq_empty, and_imp],
      refine λ qc qc' hqc hqc', ⟨∅, ∅, _⟩,
      rw [hqc, hqc', to_query_count_empty],
      tauto },
    { intros i ts il hts hil h qc qc' h',
      rw [to_query_count_add_values] at h',
      have : il.to_query_count = (qc + qc').decrement i ts.length,
      by rw [← h', decrement_increment_eq_self],
      rw [decrement_add_eq_add_decrement] at this,
      specialize h _ _ this,
      obtain ⟨il₁', il₂', hil', h1, h2⟩ := h,
      refine ⟨il₁'.add_values (ts.take (qc.get_count i)),
        il₂'.add_values (ts.drop (qc.get_count i)), _, _, _⟩,
      { refine fun_like.ext_iff.2 (λ j, _),
        by_cases hj : i = j,
        { induction hj,
          have h : i ∉ (il₁' + il₂').active_oracles := hil'.symm ▸ hil,
          rw [active_oracles_add, finset.not_mem_union] at h,
          simp only [apply_eq_nil, hil, h.1, h.2, add_apply, add_values_apply, eq_self_iff_true,
            not_false_iff, list.nil_append, dite_eq_ite, if_true, list.take_append_drop] },
        { simp only [hj, ←hil', add_apply, not_false_iff, add_values_apply, dif_neg] } },
      { rw [to_query_count_add_values, h1, increment_decrement_eq_self_iff, list.length_take] },
      { rw [to_query_count_add_values, h2, list.length_drop, increment_decrement_eq_self_iff,
          eq_comm, min_eq_right_iff],
        have := congr_arg (λ qc, get_count qc i) h',
        simp only [get_count_eq_zero _ hil, get_count_increment, get_count_to_query_count,
          eq_self_iff_true, if_true, zero_add, get_count_add] at this,
        rw [this, add_tsub_cancel_left] } } },
  { obtain ⟨il₁, il₂, h1, h2⟩ := h,
    rw [← h1, to_query_count_add, h2.1, h2.2] }
end

lemma add_eq_add_iff_eq_and_eq {il il' jl jl' : spec.indexed_list τ}
  (h : il.to_query_count = jl.to_query_count) :
  il + il' = jl + jl' ↔ il = jl ∧ il' = jl' :=
begin
  refine ⟨λ h', _, λ h', by rw [h'.1, h'.2]⟩,
  simp only [fun_like.ext_iff, add_apply] at ⊢ h h',
  refine forall_and_distrib.1 (λ i, _),
  specialize h' i,
  have hil : (il i).length = (jl i).length,
  by simpa [get_count_eq_length_apply] using h i,
  have := congr_arg (list.take (il i).length) h',
  rw [list.take_left, hil, list.take_left] at this,
  rw [this, list.append_right_inj] at h',
  exact ⟨this, h'⟩
end

end to_query_count

/-- View any `indexed_list` as a `query_count` by replacing all values with `()`. -/
instance coe_query_count (τ : spec.ι → Type) : has_coe (spec.indexed_list τ) (spec.query_count) :=
{ coe := to_query_count }

@[simp] lemma coe_query_count_eq {τ : spec.ι → Type} (il : spec.indexed_list τ) :
  (↑il : spec.query_count) = il.to_query_count := rfl

end indexed_list

end oracle_spec