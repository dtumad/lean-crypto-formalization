/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec
import algebra.big_operators.basic
import algebra.indicator_function

/-!
# Lists Indexed by Oracles

This file defines a `indexed_list` structure for tracking information about queries to oracles,
keeping a list of values for each of the oracles in a given `oracle_spec`.
The structure also contains a finite set `active_oracles` of indices with non-empty tracking sets,
ensuring that only finitely many oracles are actively being tracked at once.

This is used to define a number of other types, all as specific instances:
* `query_seed` tracks pre-computed seed values for results of oracle queries.
* `query_count` tracks the number of queries made to during computation.
* `query_log` tracks the input and output values of queries to each of the oracles.
-/

namespace oracle_spec

open_locale big_operators

variables {α β γ : Type} {spec : oracle_spec} {τ τ' : spec.ι → Type}

/-- Structure for lists of values indexed by a set of oracles given by an `oracle_spec`.
`to_fun` gives the list associated to an index, where the type may depend on the index.
We also require a finset `active_oracles` containing exactly the indices with non-empty lists.
This aligns with a regular list type, which can only contain finitely many values. -/
@[ext] structure indexed_list (spec : oracle_spec) (τ : spec.ι → Type) :=
(to_fun (i : spec.ι) : list (τ i))
(active_oracles : finset spec.ι)
(mem_active_oracles_iff' (i : spec.ι) : i ∈ active_oracles ↔ to_fun i ≠ [])

/-- View an `indexed_list` as a function from oracle index to a list of values. -/
instance indexed_list.fun_like (spec : oracle_spec) (τ : spec.ι → Type) :
  fun_like (spec.indexed_list τ) spec.ι (λ i, list (τ i)) :=
{ coe := indexed_list.to_fun,
  coe_injective' := λ qs qs' h, indexed_list.ext qs qs' h (finset.ext (λ i,
    by rw [qs.mem_active_oracles_iff', qs'.mem_active_oracles_iff', h])) }

lemma indexed_list.coe_fun_eq_to_fun (il : spec.indexed_list τ)
  (i : spec.ι) : il i = il.to_fun i := rfl

namespace indexed_list

variables (il il' : spec.indexed_list τ)

section apply

lemma mem_active_oracles_iff (i) : i ∈ il.active_oracles ↔ il i ≠ [] :=
il.mem_active_oracles_iff' i

lemma not_mem_active_oracles_iff (i) : i ∉ il.active_oracles ↔ il i = [] :=
by simp [mem_active_oracles_iff]

lemma mem_active_oracles {i} (hi : il i ≠ []) : i ∈ il.active_oracles :=
(il.mem_active_oracles_iff i).2 hi

lemma mem_active_oracles' {i t ts} (hi : il i = t :: ts) : i ∈ il.active_oracles :=
il.mem_active_oracles (hi.symm ▸ list.cons_ne_nil t ts)

lemma mem_active_oracles_of_mem {i t} (hi : t ∈ il i) : i ∈ il.active_oracles :=
il.mem_active_oracles (list.ne_nil_of_mem hi)

lemma not_mem_active_oracles {i} (hi : il i = []) : i ∉ il.active_oracles :=
(il.not_mem_active_oracles_iff i).2 hi

@[simp] lemma apply_eq_nil_iff (i) : il i = [] ↔ i ∉ il.active_oracles :=
by simp [mem_active_oracles_iff]

@[simp] lemma apply_eq_nil {i} (hi : i ∉ il.active_oracles) : il i = [] :=
(apply_eq_nil_iff il i).2 hi

lemma apply_ne_nil_iff (i) : il i ≠ [] ↔ i ∈ il.active_oracles :=
(il.mem_active_oracles_iff i).symm

lemma apply_ne_nil {i} (hi : i ∈ il.active_oracles) : il i ≠ [] := (apply_ne_nil_iff il i).2 hi

@[simp] lemma apply_empty_iff (i) : (il i).empty ↔ i ∉ il.active_oracles :=
by simp [list.empty_iff_eq_nil]

lemma apply_empty {i} (hi : i ∉ il.active_oracles) : (il i).empty := (il.apply_empty_iff i).2 hi

@[simp] protected lemma ite_apply (p : Prop) [decidable p] (i) :
  (if p then il else il') i = if p then il i else il' i :=
by split_ifs; refl

lemma mem_active_oracles_of_length_ne_zero {i} (h : (il i).length ≠ 0) : i ∈ il.active_oracles :=
il.mem_active_oracles (λ hn, h (list.length_eq_zero.2 hn))

lemma mem_active_oracles_of_length_pos {i} (h : 0 < (il i).length) : i ∈ il.active_oracles :=
il.mem_active_oracles (list.length_pos_iff_ne_nil.1 h)

lemma mem_active_oracles_iff_nth_ne_none (i) : i ∈ il.active_oracles ↔ (il i).nth 0 ≠ none :=
by rw [mem_active_oracles_iff, ne.def, ne.def, list.nth_eq_none_iff,
  not_le, list.length_pos_iff_ne_nil]

end apply

section get_count

/-- The number of elements in the list at index `i`. -/
def get_count (il : spec.indexed_list τ) (i : spec.ι) : ℕ := (il i).length

lemma get_count_eq_length_apply (i) : il.get_count i = (il i).length := rfl

@[simp] lemma get_count_eq_zero_iff (i) : il.get_count i = 0 ↔ i ∉ il.active_oracles :=
by simp [list.length_eq_zero, get_count]

lemma get_count_eq_zero {i} (h : i ∉ il.active_oracles) : il.get_count i = 0 :=
(il.get_count_eq_zero_iff i).2 h

lemma get_count_ne_zero_iff (i) : il.get_count i ≠ 0 ↔ i ∈ il.active_oracles :=
iff.not_left (il.get_count_eq_zero_iff i)

lemma get_count_ne_zero {i} (h : i ∈ il.active_oracles) : il.get_count i ≠ 0 :=
(il.get_count_ne_zero_iff i).2 h

@[simp] lemma get_count_pos_iff (i) : 0 < il.get_count i ↔ i ∈ il.active_oracles :=
by simp [pos_iff_ne_zero]

lemma get_count_pos {i} (h : i ∈ il.active_oracles) : 0 < il.get_count i :=
(il.get_count_pos_iff i).2 h

@[simp] lemma one_le_get_count_iff (i) : 1 ≤ il.get_count i ↔ i ∈ il.active_oracles :=
by simp [nat.succ_le_iff]

lemma one_le_get_count {i} (h : i ∈ il.active_oracles) : 1 ≤ il.get_count i :=
(il.one_le_get_count_iff i).2 h

end get_count

section empty

/-- The empty indexed list, containing an empty list at every index. -/
def empty (spec : oracle_spec) (τ : spec.ι → Type) : spec.indexed_list τ :=
{ to_fun := λ i, [],
  active_oracles := ∅,
  mem_active_oracles_iff' := λ _, (ne_self_iff_false _).symm }

instance : has_emptyc (spec.indexed_list τ) := ⟨empty spec τ⟩

@[simp] lemma empty_apply (i) : (∅ : spec.indexed_list τ) i = [] := rfl
@[simp] lemma active_oracles_empty : (∅ : spec.indexed_list τ).active_oracles = ∅ := rfl
@[simp] lemma get_count_empty (i) : (∅ : spec.indexed_list τ).get_count i = 0 := rfl

lemma not_mem_active_oracles_empty (i) : i ∉ (∅ : spec.indexed_list τ).active_oracles :=
finset.not_mem_empty i

@[simp] lemma eq_empty_iff (il : spec.indexed_list τ) : il = ∅ ↔ il.active_oracles = ∅ :=
fun_like.ext_iff.trans (trans (by simp only [mem_active_oracles_iff, empty_apply,
  finset.not_mem_empty, iff_false, ne.def, not_not]) finset.ext_iff.symm)

lemma eq_empty_of_active_oracles_eq_empty (il : spec.indexed_list τ)
  (h : il.active_oracles = ∅) : il = ∅ := il.eq_empty_iff.2 h

end empty

section add

/-- The addition operation induced by `list.append`, where the list at each index is the first list
appended to the second, and the active oracles are those active in either of the original lists.
This forms a `add_monoid` with `∅` as the `zero` element.
In general this operation is non-commutative (see `query_count` for a case where it is). -/
def add (il il' : spec.indexed_list τ) : spec.indexed_list τ :=
{ to_fun := λ i, il i ++ il' i,
  active_oracles := il.active_oracles ∪ il'.active_oracles,
  mem_active_oracles_iff' := by simp [indexed_list.mem_active_oracles_iff',
    coe_fun_eq_to_fun, or_iff_not_imp_left] }

instance : add_cancel_monoid (spec.indexed_list τ) :=
{ add := add,
  zero := ∅,
  add_assoc := λ il il' il'', fun_like.ext _ _ (λ i, list.append_assoc (il i) (il' i) (il'' i)),
  zero_add := λ il, fun_like.ext _ _ (λ i, (il i).nil_append),
  add_zero := λ il, fun_like.ext _ _ (λ i, (il i).append_nil),
  add_left_cancel := λ il il' il'' h, begin
    simp [fun_like.ext_iff, add] at h ⊢,
    refine λ i, list.append_left_cancel (h i)
  end,
  add_right_cancel := λ il il' il'' h, begin
    simp [fun_like.ext_iff, add] at h ⊢,
    refine λ i, list.append_right_cancel (h i),
  end }

@[simp] lemma add_apply (i) : (il + il') i = il i ++ il' i := rfl
@[simp] lemma active_oracles_add : (il + il').active_oracles =
  il.active_oracles ∪ il'.active_oracles := rfl
@[simp] lemma get_count_add (i) : (il + il').get_count i = il.get_count i + il'.get_count i :=
by simp_rw [get_count_eq_length_apply, add_apply, list.length_append]

lemma mem_active_oracles_add_left {i} (hi : i ∈ il.active_oracles) :
  i ∈ (il + il').active_oracles := finset.mem_union_left _ hi

lemma mem_active_oracles_add_right {i} (hi : i ∈ il'.active_oracles) :
  i ∈ (il + il').active_oracles := finset.mem_union_right _ hi

lemma zero_eq_empty : (0 : spec.indexed_list τ) = ∅ := rfl
@[simp] lemma zero_apply (i) : (0 : spec.indexed_list τ) i = [] := rfl
@[simp] lemma active_oracles_zero : (0 : spec.indexed_list τ).active_oracles = ∅ := rfl
@[simp] lemma get_count_zero (i) : (0 : spec.indexed_list τ).get_count i = 0 := rfl

@[simp] lemma add_empty : il + ∅ = il := add_zero il
@[simp] lemma empty_add : ∅ + il = il := zero_add il

lemma list_sum_apply (qcs : list (spec.indexed_list τ)) (i : spec.ι) :
  qcs.sum i = (qcs.map (λ (qc : spec.indexed_list τ), qc i)).join :=
begin
  induction qcs with qc qcs hqcs,
  { simp only [list.join, list.sum_nil, zero_apply, list.map_nil] },
  { simp only [hqcs, list.join, list.map, list.sum_cons, add_apply] }
end

@[simp] lemma add_left_eq_self_iff : il + il' = il' ↔ il = ∅ :=
by rw [add_left_eq_self, zero_eq_empty]

@[simp] lemma add_right_eq_self_iff : il + il' = il ↔ il' = ∅ :=
by rw [add_right_eq_self, zero_eq_empty]

lemma add_comm_of_active_oracles_disjoint
  (h : disjoint il.active_oracles il'.active_oracles) : il + il' = il' + il :=
begin
  rw [finset.disjoint_iff_inter_eq_empty] at h,
  refine fun_like.ext _ _ (λ i, _),
  by_cases hi : i ∈ il.active_oracles,
  { have hi' : i ∉ il'.active_oracles,
    from λ hi', (finset.not_mem_empty i (h ▸ finset.mem_inter.2 ⟨hi, hi'⟩)),
    simp only [hi', add_apply, apply_eq_nil, not_false_iff, list.append_nil, list.nil_append] },
  { simp only [hi, add_apply, apply_eq_nil, not_false_iff, list.nil_append, list.append_nil] }
end

end add

section of_list

/-- Create an indexed list from a list of elements corresponding to a particular index,
using an empty list for all the other indices besides that one. -/
def of_list {i} (ts : list (τ i)) : spec.indexed_list τ :=
{ to_fun := λ i', if h : i = i' then h.rec_on ts else [],
  active_oracles := if ts.empty then ∅ else {i},
  mem_active_oracles_iff' := λ i', begin
    by_cases hi : i = i',
    { induction hi,
      cases ts; simp },
    { cases ts;
      simp [hi, ne.symm hi] }
  end }

variables {i : spec.ι} (ts ts' : list (τ i))

@[simp] lemma of_list_apply (i') : of_list ts i' = if h : i = i' then h.rec_on ts else [] := rfl

@[simp] lemma active_oracles_of_list : (of_list ts).active_oracles =
  if ts.empty then ∅ else {i} := rfl

@[simp] lemma get_count_of_list (i') : (of_list ts).get_count i' =
  if i = i' then ts.length else 0 :=
begin
  by_cases hi : i = i',
  { induction hi,
    simp [get_count_eq_length_apply] },
  { simp [hi, get_count_eq_length_apply] }
end

lemma of_list_apply_self : of_list ts i = ts := dif_pos rfl
lemma get_count_of_list_self : (of_list ts).get_count i = ts.length := by simp

lemma mem_active_oracles_of_list_iff (i') :
  i' ∈ (of_list ts).active_oracles ↔ i = i' ∧ ts ≠ [] :=
by cases ts; simp [list.empty_iff_eq_nil, @eq_comm _ i i']

lemma mem_active_oracles_of_list (h : ts ≠ []) : i ∈ (of_list ts).active_oracles :=
let this : ¬ ts.empty := λ h', (h (list.empty_iff_eq_nil.1 h')).elim in by simp [this]

lemma of_list_apply_same_index : of_list ts i = ts := by simp

@[simp] lemma of_list_append : of_list (ts ++ ts') = of_list ts + of_list ts' :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

lemma of_list_cons (t : τ i) : of_list (t :: ts) = of_list [t] + of_list ts :=
by rw [← list.singleton_append, of_list_append]

@[simp] lemma of_list_nil : (of_list ([] : list (τ i))) = ∅ :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

@[simp] lemma of_list_inj : of_list ts = of_list ts' ↔ ts = ts' :=
⟨λ h, by simpa [of_list] using congr_arg (λ il, to_fun il i) h, λ h, congr_arg _ h⟩

lemma of_list_add_of_list_comm {j j'} (h : j ≠ j') (ts : list (τ j)) (ts' : list (τ j')) :
  of_list ts + of_list ts' = of_list ts' + of_list ts :=
add_comm_of_active_oracles_disjoint _ _ (by cases ts; cases ts'; simp [h])

end of_list

section add_values

/-- Add a list of values to an existing indexed list. -/
def add_values (il : spec.indexed_list τ) {i} (ts : list (τ i)) : spec.indexed_list τ :=
il + of_list ts

variables {i : spec.ι} (ts ts' : list (τ i))

@[simp] lemma add_values_apply (i') : il.add_values ts i' =
  if h : i = i' then h.rec_on (il i ++ ts) else il i' :=
begin
  by_cases hi : i = i',
  { induction hi,
    simp [add_values] },
  { simp [add_values, hi] }
end

@[simp] lemma active_oracles_add_values : (il.add_values ts).active_oracles =
  if ts.empty then il.active_oracles else insert i il.active_oracles :=
begin
  cases ts,
  { simp [add_values] },
  { exact finset.ext (by simp [add_values, or_comm]) }
end

@[simp] lemma get_count_add_values (i') : (il.add_values ts).get_count i' =
  il.get_count i' + if i = i' then ts.length else 0 :=
begin
  by_cases hi : i = i',
  { induction hi,
    simp [get_count_eq_length_apply] },
  { simp [hi, get_count_eq_length_apply] }
end

lemma mem_active_oracles_add_values_iff (i') :
  i' ∈ (il.add_values ts).active_oracles ↔ (i = i' ∧ ts ≠ []) ∨ i' ∈ il.active_oracles :=
by by_cases hts : ↥(ts.empty); simp [hts, ← list.empty_iff_eq_nil, @eq_comm _ i i']

lemma mem_active_oracles_add_values {i'} (hi' : i' ∈ il.active_oracles) :
  i' ∈ (il.add_values ts).active_oracles :=
by by_cases hts : ↥(ts.empty); simp [hi', hts]

lemma mem_active_oracles_add_values' (hts : ts ≠ []) :
  i ∈ (il.add_values ts).active_oracles := by simp [hts, list.empty_iff_eq_nil]

@[simp] lemma add_values_nil : il.add_values ([] : list (τ i)) = il := by simp [add_values]

@[simp] lemma add_values_add_values : (il.add_values ts).add_values ts' =
  il.add_values (ts ++ ts') := by simp [add_values, add_assoc, of_list_append]

lemma add_values_cons (t) : il.add_values (t :: ts) = (il.add_values [t]).add_values ts := by simp

end add_values

section take_at_index

/-- Take the first `n` elements of the list at index `i`, leaving the other lists unchanged. -/
def take_at_index (il : spec.indexed_list τ) (i : spec.ι) (n : ℕ) : spec.indexed_list τ :=
{ to_fun := λ i', if i = i' then (il i').take n else il i',
  active_oracles := if n = 0 then il.active_oracles.erase i else il.active_oracles,
  mem_active_oracles_iff' := λ i', begin
    cases n with n,
    { simp [@eq_comm _ i i'] },
    { by_cases hi : i = i'; simp [hi] }
  end }

variables (i : spec.ι) (n : ℕ)

@[simp] lemma take_at_index_apply (i') : il.take_at_index i n i' =
  if i = i' then (il i').take n else il i' := rfl

@[simp] lemma active_oracles_take_at_index : (il.take_at_index i n).active_oracles =
  if n = 0 then il.active_oracles.erase i else il.active_oracles := rfl

@[simp] lemma get_count_take_at_index (i') : (il.take_at_index i n).get_count i' =
  if i = i' then min n (il i').length else il.get_count i' :=
by by_cases hi : i = i'; simp [hi, get_count_eq_length_apply]

lemma mem_active_oracles_take_at_index_iff (i') : i' ∈ (il.take_at_index i n).active_oracles ↔
  (i = i' → n ≠ 0) ∧ i' ∈ il.active_oracles :=
by cases n; simp [@eq_comm _ i i', imp_false]

lemma mem_active_oracles_take_at_index {i'} (hi' : i' ∈ il.active_oracles) (hi : i ≠ i') :
  i' ∈ (il.take_at_index i n).active_oracles := by cases n; simp [hi', hi, ne.symm hi]

lemma mem_active_oracles_take_at_index_self (hn : n ≠ 0) (hi : i ∈ il.active_oracles) :
  i ∈ (il.take_at_index i n).active_oracles := by simp [hn, hi]

lemma take_at_index_empty : (∅ : spec.indexed_list τ).take_at_index i n = ∅ := by simp

lemma add_values_take_at_index_zero : (il.take_at_index i 0).add_values (il i) = il :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

lemma take_at_index_length_add_values (ts : list (τ i)) :
  (il.add_values ts).take_at_index i (il.get_count i) = il :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [get_count_eq_length_apply] },
  { simp [hi] }
end

@[simp] lemma take_at_index_of_list (ts : list (τ i)) :
  (of_list ts).take_at_index i n = of_list (ts.take n) :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

@[simp] lemma take_at_index_eq_self_iff : il.take_at_index i n = il ↔ il.get_count i ≤ n :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { simpa [get_count_eq_length_apply] using congr_arg (λ il, get_count il i) h },
  { simp [fun_like.ext_iff, list.take_all_of_le h] },
end

end take_at_index

section drop_at_index

/-- Drop the first `n` elements of the list at index `i`, leaving the other lists unchanged. -/
def drop_at_index (il : spec.indexed_list τ) (i : spec.ι) (n : ℕ) : spec.indexed_list τ :=
{ to_fun := λ i', if i = i' then (il i').drop n else il i',
  active_oracles := if n < il.get_count i then il.active_oracles else il.active_oracles.erase i,
  mem_active_oracles_iff' := λ i', begin
  by_cases hi : i = i',
  { induction hi,
    by_cases hn : n < il.get_count i,
    { have hi' : i ∈ il.active_oracles,
      from il.mem_active_oracles_of_length_pos (lt_of_le_of_lt zero_le' hn),
      simp [hn, hi', list.drop_eq_nil_iff_le, ← get_count_eq_length_apply] },
    { simp [hn, list.drop_eq_nil_iff_le, ← get_count_eq_length_apply] } },
  { by_cases hn : n < il.get_count i,
    { simp [hi, hn] },
    { simp [hi, ne.symm hi, hn] } }
  end }

variables (i : spec.ι) (n : ℕ)

@[simp] lemma drop_at_index_apply (i') : (il.drop_at_index i n) i' =
  if i = i' then (il i').drop n else il i' := rfl

@[simp] lemma active_oracles_drop_at_index : (il.drop_at_index i n).active_oracles =
  if n < il.get_count i then il.active_oracles else il.active_oracles.erase i := rfl

@[simp] lemma get_count_drop_at_index (i') : (il.drop_at_index i n).get_count i' =
  il.get_count i' - if i = i' then n else 0 :=
by by_cases hi : i = i'; simp [hi, get_count_eq_length_apply]

lemma mem_active_oracles_drop_at_index_iff (i') : i' ∈ (il.drop_at_index i n).active_oracles ↔
  (i = i' → n < il.get_count i) ∧ i' ∈ il.active_oracles :=
by by_cases hn : n < il.get_count i; simp [hn, imp_false, @eq_comm _ i i']

lemma mem_active_oracles_drop_at_index {i'} (hi' : i' ∈ il.active_oracles)
  (hi : i ≠ i') : i' ∈ (il.drop_at_index i n).active_oracles :=
(mem_active_oracles_drop_at_index_iff il i n i').2 ⟨λ h, (hi h).elim, hi'⟩

lemma mem_active_oracles_drop_at_index_self (hi : i ∈ il.active_oracles)
  (hn : n < il.get_count i) : i ∈ (il.drop_at_index i n).active_oracles :=
(mem_active_oracles_drop_at_index_iff il i n i).2 ⟨λ h, hn, hi⟩

@[simp] lemma drop_at_index_zero : il.drop_at_index i 0 = il :=
fun_like.ext _ _ (λ i', by simp)

lemma drop_at_index_empty : (∅ : spec.indexed_list τ).drop_at_index i n = ∅ := by simp

@[simp] lemma drop_at_index_add : (il + il').drop_at_index i n =
  il.drop_at_index i n + il'.drop_at_index i (n - il.get_count i) :=
fun_like.ext _ _ (λ i', by by_cases hi : i = i';
  simp [hi, list.drop_append_eq_append_drop, get_count_eq_length_apply])

@[simp] lemma drop_at_index_of_list_singleton {i} (t : τ i) :
  (of_list [t]).drop_at_index i n = if n = 0 then of_list [t] else ∅ :=
by cases n with n; simp

lemma drop_at_index_of_list_eq_empty {i} (ts : list (τ i)) (hn : ts.length ≤ n) :
  (of_list ts).drop_at_index i n = ∅ :=
begin
  simp [lt_iff_not_le, hn],
  split_ifs; simp
end

@[simp] lemma drop_at_index_succ_of_list_succ {i} (t : τ i) (ts : list (τ i)) :
  (of_list (t :: ts)).drop_at_index i (n + 1) = (of_list ts).drop_at_index i n :=
by { rw [of_list_cons], simp [drop_at_index_add] }

lemma drop_at_index_eq_self {i} (h : i ∉ il.active_oracles) : il.drop_at_index i n = il :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [il.apply_eq_nil h] },
  { simp [hi] }
end

lemma drop_at_index_eq_drop_at_index {i} {n m : ℕ} (h : n = m ∨ il.get_count i ≤ min n m) :
  il.drop_at_index i n = il.drop_at_index i m :=
begin
  rw [le_min_iff] at h,
  refine h.rec_on (λ hn, congr_arg _ hn) (λ hil, fun_like.ext _ _ (λ i', _)),
  by_cases hi : i = i',
  { induction hi,
    simp [list.drop_eq_nil_of_le hil.1, list.drop_eq_nil_of_le hil.2] },
  { simp only [hi, drop_at_index_apply, if_false] }
end

lemma of_list_add_eq_iff {i} (ts : list (τ i)) : of_list ts + il = il' ↔
  ts = (il' i).take ts.length ∧ il = il'.drop_at_index i ts.length :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { induction h,
    simp [zero_eq_empty, apply_ite (finset.erase), ite_apply] },
  { rw [h.1, h.2],
    refine fun_like.ext _ _ (λ i', _),
    by_cases hi : i = i',
    { induction hi,
      simp },
    { simp [hi] } }
end

lemma add_drop_at_index_eq_self : of_list ((il i).take n) + il.drop_at_index i n = il :=
begin
  refine (of_list_add_eq_iff _ _ _).2 _,
  by_cases hi : (il i).length ≤ n,
  { simp [list.length_take, min_eq_right hi, list.take_all_of_le hi],
    refine drop_at_index_eq_drop_at_index il (or.inr (le_min hi le_rfl)) },
  { simp [list.length_take, min_eq_left (le_of_not_le hi)] }
end

lemma drop_at_index_get_count : il.drop_at_index i (il.get_count i) = il.take_at_index i 0 :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [get_count_eq_length_apply] },
  { simp [hi] }
end

end drop_at_index

section map

def map (il : spec.indexed_list τ) (f : Π (i : spec.ι), τ i → τ' i) : spec.indexed_list τ' :=
{ to_fun := λ i, (il i).map (f i),
  active_oracles := il.active_oracles,
  mem_active_oracles_iff' := by simp }

variables (f : Π (i : spec.ι), τ i → τ' i)

@[simp] lemma map_apply (i) : il.map f i = (il i).map (f i) := rfl
@[simp] lemma active_oracles_map : (il.map f).active_oracles = il.active_oracles := rfl
@[simp] lemma get_count_map : (il.map f).get_count = il.get_count :=
by simp [function.funext_iff, get_count_eq_length_apply]

lemma mem_active_oracles_map {i} (hi : i ∈ il.active_oracles) : i ∈ (il.map f).active_oracles := hi

lemma map_empty : (∅ : spec.indexed_list τ).map f = ∅ := by simp

@[simp] lemma map_add : (il + il').map f = il.map f + il'.map f := by simp [fun_like.ext_iff]

@[simp] lemma map_of_list {i} (ts : list (τ i)) : (of_list ts).map f = of_list (ts.map (f i)) :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

@[simp] lemma map_add_values {i} (ts : list (τ i)) :
  (il.add_values ts).map f = (il.map f).add_values (ts.map (f i)) :=
by simp [add_values]

@[simp] lemma map_take_at_index (i : spec.ι) (n : ℕ) :
  (il.take_at_index i n).map f = (il.map f).take_at_index i n :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [list.map_take] },
  { simp [hi] }
end

@[simp] lemma map_drop_at_index (i : spec.ι) (n : ℕ) :
  (il.drop_at_index i n).map f = (il.map f).drop_at_index i n :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [list.map_drop] },
  { simp [hi] }
end

end map

lemma eq_empty_or_exists_eq_add_values (il : spec.indexed_list τ) : il = ∅ ∨
  ∃ (il' : spec.indexed_list τ) i (ts : list (τ i)), il = il'.add_values ts ∧ il' i = [] :=
begin
  rw [or_iff_not_imp_left],
  intro hil,
  have : ∃ (x : spec.ι), x ∈ il.active_oracles,
  by simpa [finset.eq_empty_iff_forall_not_mem] using hil,
  obtain ⟨i, hi⟩ := this,
  refine ⟨il.take_at_index i 0, i, il i, fun_like.ext _ _ (λ i', _), by simp⟩,
  { by_cases hi' : i = i',
    { induction hi',
      simp },
    { simp [hi'] } }
end

/-- To prove a property about indexed lists, it suffices to prove it for the empty list,
and to show that if it holds for an indexed list `il` then it still holds after adding values
to one particular index, where that index is initially empty. -/
theorem add_values_induction {p : spec.indexed_list τ → Prop} (il : spec.indexed_list τ)
  (h₁ : p ∅) (h₂ : ∀ ⦃i : spec.ι⦄ (ts : list (τ i)) (il : spec.indexed_list τ),
    ts ≠ [] → i ∉ il.active_oracles → p il → p (il.add_values ts)) : p il :=
begin
  cases il,
  induction il_active_oracles using finset.induction_on with i' s hsi hs generalizing il_to_fun,
  { convert h₁ using 1,
    exact eq_empty_of_active_oracles_eq_empty _ rfl },
  { rw [← add_values_take_at_index_zero ({to_fun := il_to_fun, active_oracles := insert i' s,
      mem_active_oracles_iff' := _}) i'],
    refine h₂ _ _ _ _ _,
    { simpa [coe_fun_eq_to_fun] using il_mem_active_oracles_iff' i' },
    { simp },
    { simp [take_at_index, hsi, hs] } }
end

section sums

lemma list_sum_apply_eq_join_map (ils : list (spec.indexed_list τ)) (i) :
  ils.sum i = (ils.map (λ (il : spec.indexed_list τ), il i)).join :=
begin
  induction ils with il ils hil,
  { refl },
  { rw [list.sum_cons, add_apply, hil, list.map_cons, list.join] }
end

lemma list_sum_apply_eq_filter_mem_active_oracles (ils : list (spec.indexed_list τ)) (i) :
  ils.sum i = (ils.filter (λ il, i ∈ active_oracles il)).sum i :=
begin
  induction ils with il ils hil,
  { refl },
  { by_cases hi : i ∈ il.active_oracles,
    { simp [hi, hil] },
    { simp [hi, hil, apply_eq_nil _ hi] } }
end

end sums

section filter_oracles

noncomputable def filter_oracles (il : spec.indexed_list τ)
  (s : set spec.ι) [decidable_pred (∈ s)] : spec.indexed_list τ :=
{ to_fun := λ i, if i ∈ s then il i else [],
  active_oracles := {x ∈ il.active_oracles | x ∈ s},
  mem_active_oracles_iff' := by simp [and_comm] }

variables (s : set spec.ι)
variable [decidable_pred (∈ s)]

@[simp] lemma filter_oracles_apply (i) :
  (il.filter_oracles s) i = if i ∈ s then il i else [] := rfl

@[simp] lemma active_oracles_filter_oracles :
  (il.filter_oracles s).active_oracles = {x ∈ il.active_oracles | x ∈ s} := rfl

@[simp] lemma active_oracles_filter_oracles' (s : finset spec.ι) :
  (il.filter_oracles s).active_oracles = il.active_oracles ∩ s :=
finset.ext (λ i', by simp)

@[simp] lemma get_count_filter_oracles (i) : (il.filter_oracles s).get_count i =
  if i ∈ s then il.get_count i else 0 := by split_ifs with hs; simp [get_count_eq_length_apply, hs]

lemma mem_active_oracles_filter_oracles_iff (i) :
  i ∈ (il.filter_oracles s).active_oracles ↔ i ∈ il.active_oracles ∧ i ∈ s := by simp

@[simp] lemma filter_oracles_empty_eq_empty : il.filter_oracles ∅ = ∅ := by simp [fun_like.ext_iff]

@[simp] lemma filter_oracles_eq_self_iff :
  il.filter_oracles s = il ↔ ∀ i ∈ il.active_oracles, i ∈ s :=
by simp [fun_like.ext_iff, not_imp_not, @eq_comm _ []]

@[simp] lemma filter_oracles_eq_self_iff' (s : finset spec.ι) :
  il.filter_oracles s = il ↔ il.active_oracles ⊆ s :=
by simp only [finset.subset_iff, filter_oracles_eq_self_iff, finset.mem_coe]

lemma filter_oracles_self (s : finset spec.ι) : il.filter_oracles il.active_oracles = il :=
by simp only [filter_oracles_eq_self_iff', finset.subset.refl]

@[simp] lemma filter_oracles_index_eq (i) : il.filter_oracles ((=) i) = of_list (il i) :=
begin
  simp [fun_like.ext_iff, set.mem_def],
  intro i',
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

end filter_oracles

section has_sep

noncomputable instance : has_sep spec.ι (spec.indexed_list τ) :=
{ sep := λ p il, @filter_oracles _ _ il p (classical.dec_pred p)}

variable (p : spec.ι → Prop)

lemma sep_eq_filter : {i ∈ il | p i} = @filter_oracles _ _ il p (classical.dec_pred p) := rfl

lemma sep_eq_filter' [decidable_pred p] : {i ∈ il | p i} = il.filter_oracles p := by convert rfl

@[simp] lemma sep_apply (i) : {x ∈ il | p x} i = (@ite _ (p i) (classical.dec _) (il i) []) := rfl

@[simp] lemma sep_apply' [decidable_pred p] (i) : {x ∈ il | p x} i = if p i then il i else [] :=
by simpa only [sep_eq_filter']

@[simp] lemma active_oracles_sep : {x ∈ il | p x}.active_oracles =
  {x ∈ il.active_oracles | p x} := rfl

lemma mem_active_oracles_sep_iff (i : spec.ι) :
  i ∈ {x ∈ il | p x}.active_oracles ↔ i ∈ il.active_oracles ∧ p i :=
by simp only [active_oracles_sep, finset.sep_def, finset.mem_filter]

@[simp] lemma get_count_sep (i) : {x ∈ il | p x}.get_count i =
  (@ite _ (p i) (classical.dec _) (il.get_count i) 0) :=
by simp [get_count_eq_length_apply, apply_ite list.length]

@[simp] lemma sep_false_eq_empty : {i ∈ il | false} = ∅ :=
by simp only [eq_empty_iff, active_oracles_sep, finset.sep_def, finset.filter_false]

@[simp] lemma sep_eq_self_iff : {x ∈ il | p x} = il ↔ ∀ i ∈ il.active_oracles, p i :=
by simpa [sep_eq_filter]

@[simp] lemma sep_self : {i ∈ il | i ∈ il.active_oracles} = il :=
by simp only [sep_eq_self_iff, imp_self, implies_true_iff]

@[simp] lemma sep_index_eq (j) : {i ∈ il | i = j} = of_list (il j) :=
begin
  convert filter_oracles_index_eq il j,
  rw [sep_eq_filter],
  congr,
  simp [set.ext_iff, set.mem_def, @eq_comm _ j],
end

end has_sep

end indexed_list

end oracle_spec