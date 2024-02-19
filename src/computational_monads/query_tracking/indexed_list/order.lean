/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.indexed_list.basic

/-!
# Ordering on Indexed Lists

This file defines an order on `indexed_list spec τ`, where `il ≤ il'` iff
the list at each index in `il` is a prefix of the list in `il'`.
In the case of `query_seed` this corresponds to having only a partial seed,
and for `query_count` it corresponds to every individual count being lower.
-/

namespace oracle_spec

namespace indexed_list

variables {α β γ : Type} {spec : oracle_spec} {τ τ' : spec.ι → Type}

section partial_order

/-- Ordering on indexed lists induced by list prefixes, specifically we say `il ≤ il'`
if every list in `il` is a prefix of the corresponding list in `il'`. -/
instance : partial_order (spec.indexed_list τ) :=
{ le := λ il il', ∀ i, il i <+: il' i,
  le_refl := λ il i, refl (il i),
  le_trans := λ il il' il'' hil hil' i, trans (hil i) (hil' i),
  le_antisymm := λ il il' hil hil', fun_like.ext il il' (λ i, antisymm (hil i) (hil' i)) }

lemma le_iff_forall_prefix (il il' : spec.indexed_list τ) :
  il ≤ il' ↔ ∀ i, il i <+: il' i := iff.rfl

lemma exists_eq_append_of_le {il il' : spec.indexed_list τ} (h : il ≤ il') (i) :
  ∃ (ts : list (τ i)), il i ++ ts = il' i := h i

end partial_order

section order_bot

/-- The empty indexed list behaves like a bottom element with the prefix ordering. -/
instance : order_bot (spec.indexed_list τ) :=
{ bot := ∅,
  bot_le := λ il i, (il i).nil_prefix }

@[simp] lemma bot_eq_empty : (⊥ : spec.indexed_list τ) = ∅ := rfl
@[simp] lemma empty_le (il : spec.indexed_list τ) : ∅ ≤ il := bot_le
@[simp] lemma le_empty_iff (il : spec.indexed_list τ) : il ≤ ∅ ↔ il = ∅ := le_bot_iff
@[simp] protected lemma zero_le (il : spec.indexed_list τ) : 0 ≤ il := bot_le
@[simp] protected lemma le_zero_iff (il : spec.indexed_list τ) : il ≤ 0 ↔ il = 0 := le_bot_iff

end order_bot

section semilattice_inf

section inf_aux

/-- Helper function for constructing the index-wise elements of `il ⊓ il'`. -/
protected def inf_aux [decidable_eq α] : list α → list α → list α
| (t :: ts) (t' :: ts') := if t = t' then t :: inf_aux ts ts' else []
| _ _ := []

@[simp] protected lemma inf_aux_nil_left [decidable_eq α] (ts : list α) :
  indexed_list.inf_aux [] ts = [] := rfl

@[simp] protected lemma inf_aux_nil_right [decidable_eq α] (ts : list α) :
  indexed_list.inf_aux ts [] = [] := by cases ts; refl

@[simp] protected lemma inf_aux_cons [decidable_eq α] (ts ts' : list α) (t t' : α) :
  indexed_list.inf_aux (t :: ts) (t' :: ts') =
    if t = t' then t :: indexed_list.inf_aux ts ts' else [] := rfl

@[simp] protected lemma length_inf_aux_of_subsingleton [subsingleton α] (ts ts' : list α) :
  (indexed_list.inf_aux ts ts').length = min ts.length ts'.length :=
begin
  induction ts with t ts h generalizing ts',
  { simp },
  { cases ts' with t' ts',
    { simp } ,
    { simp [h, min_add_add_right] } }
end

@[simp] protected lemma inf_aux_self [decidable_eq α] :
  Π (ts : list α), indexed_list.inf_aux ts ts = ts
| (t :: ts) := by simp [indexed_list.inf_aux, inf_aux_self ts]
| [] := by simp [indexed_list.inf_aux]

@[simp] protected lemma inf_aux_append [decidable_eq α] (ts ts' ts'' : list α) :
  indexed_list.inf_aux (ts ++ ts') (ts ++ ts'') = ts ++ indexed_list.inf_aux ts' ts'' :=
begin
  induction ts with t ts hts,
  { simp },
  { simp [list.cons_append, indexed_list.inf_aux, hts] }
end

@[simp] protected lemma inf_aux_prefix_left [decidable_eq α] : Π (ts ts' : list α),
  indexed_list.inf_aux ts ts' <+: ts
| (t :: ts) (t' :: ts') := by by_cases ht : t = t'; simp [ht, indexed_list.inf_aux,
    list.cons_prefix_iff, inf_aux_prefix_left ts ts', list.nil_prefix]
| (t :: ts) [] := list.nil_prefix _
| [] _ := list.nil_prefix _

@[simp] protected lemma inf_aux_prefix_right [decidable_eq α] : Π (ts ts' : list α),
  indexed_list.inf_aux ts ts' <+: ts'
| (t :: ts) (t' :: ts') := by by_cases ht : t = t'; simp [ht, indexed_list.inf_aux,
    list.cons_prefix_iff, inf_aux_prefix_right ts ts', list.nil_prefix]
| (t :: ts) [] := list.nil_prefix _
| [] _ := list.nil_prefix _

end inf_aux

/-- Inf operation for the order given by taking the matching portions of each individual list. -/
noncomputable def inf (il il' : spec.indexed_list τ) : spec.indexed_list τ :=
{ to_fun := λ i, @indexed_list.inf_aux _ (classical.dec_eq _) (il i) (il' i),
  active_oracles := {i ∈ il.active_oracles | (il i).nth 0 = (il' i).nth 0},
  mem_active_oracles_iff' := λ i, begin
    rw [finset.sep_def, finset.mem_filter, ne.def, mem_active_oracles_iff],
    induction (il i); induction (il' i); simp [indexed_list.inf_aux]
  end }

noncomputable instance : semilattice_inf (spec.indexed_list τ) :=
{ inf := inf,
  le_inf := λ il il' il'' hil hil' i, begin
    haveI : decidable_eq (τ i) := classical.dec_eq (τ i),
    obtain ⟨ts, hts⟩ := hil i,
    obtain ⟨ts', hts'⟩ := hil' i,
    refine ⟨indexed_list.inf_aux ts ts', _⟩,
    simp [inf, coe_fun_eq_to_fun] at ⊢ hts hts',
    simp [← hts, ← hts'],
    congr
  end,
  inf_le_left := λ il il' i, begin
    haveI : decidable_eq (τ i) := classical.dec_eq (τ i),
    convert indexed_list.inf_aux_prefix_left _ _,
  end,
  inf_le_right := λ il il' i, begin
    haveI : decidable_eq (τ i) := classical.dec_eq (τ i),
    convert indexed_list.inf_aux_prefix_right _ _,
  end,
  .. indexed_list.partial_order }

variables (il il' : spec.indexed_list τ)

@[simp] lemma inf_empty : il ⊓ ∅ = ∅ := inf_bot_eq
@[simp] lemma empty_inf : ∅ ⊓ il = ∅ := bot_inf_eq

@[simp] lemma active_oracles_inf : (il ⊓ il').active_oracles =
  {i ∈ il.active_oracles | (il i).nth 0 = (il' i).nth 0} := rfl

@[simp] lemma inf_apply (i : spec.ι) : (il ⊓ il') i =
  @indexed_list.inf_aux _ (classical.dec_eq _) (il i) (il' i) := rfl

end semilattice_inf

variables (il il' : spec.indexed_list τ)

lemma exists_eq_add_of_le {il il' : spec.indexed_list τ} (h : il ≤ il') :
  ∃ ilx, il + ilx = il' :=
⟨{ to_fun := λ i, (il' i).drop (il.get_count i),
   active_oracles := {i ∈ il'.active_oracles | il.get_count i < il'.get_count i},
   mem_active_oracles_iff' := begin
    simp [list.drop_eq_nil_iff_le, and_iff_right_iff_imp, get_count_eq_length_apply],
    intros i h,
    refine mem_active_oracles_of_length_pos _ (lt_of_le_of_lt zero_le' h),
   end}
, begin
  simp [fun_like.ext_iff],
  intro i,
  obtain ⟨xs, h⟩ := h i,
  refine trans _ (list.take_append_drop (il.get_count i) (il' i)),
  refine congr_arg (λ xs, xs ++ list.drop (il.get_count i) (il' i)) _,
  rw [← h, get_count_eq_length_apply, list.take_append_of_le_length le_rfl, list.take_length],
end⟩

@[simp] lemma le_self_add : il ≤ il + il' :=
λ i, list.prefix_append (il i) (il' i)

@[simp] lemma le_add_values {i} (ts : list (τ i)) : il ≤ il.add_values ts :=
by simp only [add_values, le_self_add]

@[simp] lemma take_at_index_le (i n) : il.take_at_index i n ≤ il :=
begin
  refine λ i', _,
  by_cases hi : i = i',
  { induction hi,
    simp [list.take_prefix _ _] },
  { simp [hi] }
end

lemma get_count_le_get_count {il il' : spec.indexed_list τ}
  (h : il ≤ il') (i : spec.ι) : il.get_count i ≤ il'.get_count i :=
list.is_prefix.length_le (h i)

end indexed_list

end oracle_spec