/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec
import algebra.big_operators.basic

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

lemma not_mem_active_oracles {i} (hi : il i = []) : i ∉ il.active_oracles :=
(il.not_mem_active_oracles_iff i).2 hi

@[simp] lemma apply_eq_nil_iff (i) : il i = [] ↔ i ∉ il.active_oracles :=
by simp [mem_active_oracles_iff]

lemma apply_eq_nil {i} (hi : i ∉ il.active_oracles) : il i = [] := (apply_eq_nil_iff il i).2 hi

lemma apply_ne_nil_iff (i) : il i ≠ [] ↔ i ∈ il.active_oracles :=
(il.mem_active_oracles_iff i).symm

lemma apply_ne_nil {i} (hi : i ∈ il.active_oracles) : il i ≠ [] := (apply_ne_nil_iff il i).2 hi

@[simp] lemma apply_empty_iff (i) : (il i).empty ↔ i ∉ il.active_oracles :=
by simp [list.empty_iff_eq_nil]

lemma apply_empty {i} (hi : i ∉ il.active_oracles) : (il i).empty := (il.apply_empty_iff i).2 hi

@[simp] lemma ite_apply (p : Prop) [decidable p] (i) :
  (if p then il else il') i = if p then il i else il' i :=
by split_ifs; refl

lemma mem_active_oracles_of_length_ne_zero {i} (h : (il i).length ≠ 0) : i ∈ il.active_oracles :=
il.mem_active_oracles (λ hn, h (list.length_eq_zero.2 hn))

lemma mem_active_oracles_of_length_pos {i} (h : 0 < (il i).length) : i ∈ il.active_oracles :=
il.mem_active_oracles (list.length_pos_iff_ne_nil.1 h)

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

lemma get_count_empty (i) : (∅ : spec.indexed_list τ).get_count i = 0 := rfl

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

instance : add_monoid (spec.indexed_list τ) :=
{ add := add,
  zero := ∅,
  add_assoc := λ il il' il'', fun_like.ext _ _ (λ i, list.append_assoc (il i) (il' i) (il'' i)),
  zero_add := λ il, fun_like.ext _ _ (λ i, (il i).nil_append),
  add_zero := λ il, fun_like.ext _ _ (λ i, (il i).append_nil) }

@[simp] lemma add_apply (i) : (il + il') i = il i ++ il' i := rfl
@[simp] lemma active_oracles_add : (il + il').active_oracles =
  il.active_oracles ∪ il'.active_oracles := rfl

@[simp] lemma get_count_add (i) : (il + il').get_count i = il.get_count i + il'.get_count i :=
by simp_rw [get_count_eq_length_apply, add_apply, list.length_append]

lemma zero_eq_empty : (0 : spec.indexed_list τ) = ∅ := rfl
@[simp] lemma zero_apply (i) : (0 : spec.indexed_list τ) i = [] := rfl
@[simp] lemma active_oracles_zero : (0 : spec.indexed_list τ).active_oracles = ∅ := rfl

@[simp] lemma add_empty : il + ∅ = il := add_zero il
@[simp] lemma empty_add : ∅ + il = il := zero_add il

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

@[simp] lemma of_list_add_of_list : of_list ts + of_list ts' = of_list (ts ++ ts') :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

@[simp] lemma of_list_nil : (of_list ([] : list (τ i))) = ∅ :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp },
  { simp [hi] }
end

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

@[simp] lemma add_values_nil : il.add_values ([] : list (τ i)) = il := by simp [add_values]

@[simp] lemma add_values_add_values : (il.add_values ts).add_values ts' =
  il.add_values (ts ++ ts') := by simp [add_values, add_assoc, of_list_add_of_list]

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

end take_at_index

section drop_at_index

/-- Drop the first `n` elements of the list at index `i`, leaving the other lists unchanged. -/
def drop_at_index (il : spec.indexed_list τ) (i : spec.ι) (n : ℕ) : spec.indexed_list τ :=
{ to_fun := λ i', if i = i' then (il i').drop n else il i',
  active_oracles := if n < (il i).length then il.active_oracles else il.active_oracles.erase i,
  mem_active_oracles_iff' := λ i', begin
  by_cases hi : i = i',
  { induction hi,
    by_cases hn : n < (il i).length,
    { have hi' : i ∈ il.active_oracles,
      from il.mem_active_oracles_of_length_pos (lt_of_le_of_lt zero_le' hn),
      simp [hn, hi', list.drop_eq_nil_iff_le] },
    { simp [hn, list.drop_eq_nil_iff_le] } },
  { by_cases hn : n < (il i).length,
    { simp [hi, hn] },
    { simp [hi, ne.symm hi, hn] } }
  end }

variables (i : spec.ι) (n : ℕ)

@[simp] lemma drop_at_index_apply (i') : (il.drop_at_index i n) i' =
  if i = i' then (il i').drop n else il i' := rfl

@[simp] lemma active_oracles_drop_at_index : (il.drop_at_index i n).active_oracles =
  if n < (il i).length then il.active_oracles else il.active_oracles.erase i := rfl

@[simp] lemma get_count_drop_at_index (i') : (il.drop_at_index i n).get_count i' =
  il.get_count i' - if i = i' then n else 0 :=
by by_cases hi : i = i'; simp [hi, get_count_eq_length_apply]

lemma drop_at_index_empty : (∅ : spec.indexed_list τ).drop_at_index i n = ∅ := by simp

end drop_at_index

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

end indexed_list

end oracle_spec