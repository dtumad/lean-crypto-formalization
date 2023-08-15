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
{ le := λ il il', ∀ i, ∃ n, il i = (il' i).take n,
  le_refl := λ il i, ⟨(il i).length, symm (list.take_length (il i))⟩,
  le_trans := λ il il' il'' hil hil' i, let ⟨n, hn⟩ := hil i in let ⟨m, hm⟩ := hil' i in
    ⟨min n m, trans (hn.trans (congr_arg _ hm)) ((il'' i).take_take n m)⟩,
  le_antisymm := λ il il' hil hil', fun_like.ext il il' (λ i,
    let ⟨n, hn⟩ := hil i in let ⟨m, hm⟩ := hil' i in
    by rw [hn, hm, list.take_take, list.take_eq_take, hn, list.length_take,
      min_min_min_comm, min_self, ← min_assoc, min_comm n m, min_assoc]) }

lemma le_iff_forall_exists (il il' : spec.indexed_list τ) :
  il ≤ il' ↔ ∀ i, ∃ n, il i = (il' i).take n := iff.rfl

lemma exists_eq_take_of_le {il il' : spec.indexed_list τ} (h : il ≤ il') (i) :
  ∃ n, il i = (il' i).take n ∧ n ≤ (il' i).length :=
begin
  obtain ⟨n, hn⟩ := h i,
  refine ⟨min n (il' i).length, hn.trans _, min_le_right _ _⟩,
  rw [list.take_eq_take, min_assoc, min_self],
end

end partial_order

section order_bot

/-- The empty indexed list behaves like a bottom element with the prefix ordering. -/
instance : order_bot (spec.indexed_list τ) :=
{ bot := ∅,
  bot_le := λ il i, ⟨0, rfl⟩ }

@[simp] lemma bot_eq_empty : (⊥ : spec.indexed_list τ) = ∅ := rfl
@[simp] lemma empty_le (il : spec.indexed_list τ) : ∅ ≤ il := bot_le
@[simp] lemma le_empty_iff (il : spec.indexed_list τ) : il ≤ ∅ ↔ il = ∅ := le_bot_iff
@[simp] lemma zero_le (il : spec.indexed_list τ) : 0 ≤ il := bot_le
@[simp] lemma le_zero_iff (il : spec.indexed_list τ) : il ≤ 0 ↔ il = 0 := le_bot_iff

end order_bot

section semilattice_inf

section inf_aux

/-- Helper function for constructing the index-wise elements of `il ⊓ il'`. -/
protected def inf_aux [decidable_eq α] : list α → list α → list α
| (t :: ts) (t' :: ts') := if t = t' then t :: inf_aux ts ts' else []
| _ _ := []

@[simp] protected lemma inf_aux_self [decidable_eq α] :
  Π (ts : list α), indexed_list.inf_aux ts ts = ts
| (t :: ts) := by simp [indexed_list.inf_aux, inf_aux_self ts]
| [] := by simp [indexed_list.inf_aux]

protected lemma take_inf_aux [decidable_eq α] : Π (ts ts' : list α) (n : ℕ),
  (indexed_list.inf_aux ts ts').take n = indexed_list.inf_aux (ts.take n) (ts'.take n)
| (t :: ts) (t' :: ts') (n + 1) :=
    begin
      by_cases ht : t = t',
      { simp [list.take_cons, indexed_list.inf_aux, ht, take_inf_aux ts ts' n] },
      { simp [list.take_cons, indexed_list.inf_aux, ht] }
    end
| [] (t' :: ts') (n + 1) := by simp [indexed_list.inf_aux]
| (t :: ts) [] (n + 1) := by simp [indexed_list.inf_aux]
| [] [] (n + 1) := by simp [indexed_list.inf_aux]
| _ _ 0 := by simp [indexed_list.inf_aux]

protected lemma inf_aux_eq_take_length_left [decidable_eq α] : Π (ts ts' : list α),
  indexed_list.inf_aux ts ts' = ts.take (indexed_list.inf_aux ts ts').length
| (t :: ts) (t' :: ts') :=
    begin
      by_cases ht : t = t',
      { simpa [indexed_list.inf_aux, ht] using inf_aux_eq_take_length_left ts ts' },
      { simp [indexed_list.inf_aux, ht] }
    end
| (t :: ts) [] := by simp [indexed_list.inf_aux]
| [] (t' :: ts') := by simp [indexed_list.inf_aux]
| [] [] := by simp [indexed_list.inf_aux]

protected lemma inf_aux_eq_take_length_right [decidable_eq α] : Π (ts ts' : list α),
  indexed_list.inf_aux ts ts' = ts'.take (indexed_list.inf_aux ts ts').length
| (t :: ts) (t' :: ts') :=
    begin
      by_cases ht : t = t',
      { simpa [indexed_list.inf_aux, ht] using inf_aux_eq_take_length_right ts ts' },
      { simp [indexed_list.inf_aux, ht] }
    end
| (t :: ts) [] := by simp [indexed_list.inf_aux]
| [] (t' :: ts') := by simp [indexed_list.inf_aux]
| [] [] := by simp [indexed_list.inf_aux]

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
    obtain ⟨n, hn, hn'⟩ := exists_eq_take_of_le hil i,
    obtain ⟨m, hm, hm'⟩ := exists_eq_take_of_le hil' i,
    have : n = m := by simpa [hn', hm'] using congr_arg list.length (hn.symm.trans hm),
    refine ⟨n, _⟩,
    simp [inf, coe_fun_eq_to_fun, indexed_list.take_inf_aux] at ⊢ hn hm,
    rw [← hn, this, ← hm, indexed_list.inf_aux_self],
  end,
  inf_le_left := λ il il' i, begin
    refine ⟨(inf il il' i).length, _⟩,
    simp [inf, coe_fun_eq_to_fun],
    apply indexed_list.inf_aux_eq_take_length_left,
  end,
  inf_le_right := λ il il' i, begin
    refine ⟨(inf il il' i).length, _⟩,
    simp [inf, coe_fun_eq_to_fun],
    apply indexed_list.inf_aux_eq_take_length_right,
  end,
  .. indexed_list.partial_order }

end semilattice_inf

@[simp] lemma le_self_add (il il' : spec.indexed_list τ) : il ≤ il + il' :=
λ i, ⟨(il i).length, by simp only [add_apply, list.take_left]⟩

end indexed_list

end oracle_spec