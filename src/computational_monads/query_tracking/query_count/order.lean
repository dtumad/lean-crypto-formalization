/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.basic
import computational_monads.query_tracking.indexed_list.order

/-!
# Ordering on Query Counts

This file defines an order on `query_count`, where `qc ≤ qc'` iff the count at each index
is smaller in `qc` than in `qc'`. Note this is only a partial order.

We also define ordered addition and subtraction operations by piecewise addition and subtraction.
-/

namespace oracle_spec

open indexed_list

namespace query_count

variables {α β γ : Type} {spec : oracle_spec} (qc qc' : query_count spec)

lemma le_iff_forall_get_count_le : qc ≤ qc' ↔ ∀ i, qc.get_count i ≤ qc'.get_count i :=
⟨λ h i, let ⟨ts, hts⟩ := h i in by simp [get_count_eq_length_apply, ← hts], λ h i,
  ⟨list.replicate (qc'.get_count i - qc.get_count i) (), by simp [apply_eq_replicate_get_count,
    ← list.replicate_add, ← nat.add_sub_assoc (h i), add_comm, nat.add_sub_cancel]⟩⟩

lemma le_of_forall_get_count_le {qc qc' : query_count spec}
  (h : ∀ i, qc.get_count i ≤ qc'.get_count i) : qc ≤ qc' :=
(le_iff_forall_get_count_le qc qc').2 h

lemma get_count_le_get_count {qc qc' : query_count spec} (h : qc ≤ qc')
  (i : spec.ι) : qc.get_count i ≤ qc'.get_count i :=
(le_iff_forall_get_count_le qc qc').1 h i

section lattice

def sup (qc qc' : query_count spec) : query_count spec := (qc' - qc) + qc

/-- In the case of `query_count` we can extend the partial order on `indexed_list` to a lattice. -/
noncomputable instance : lattice (query_count spec) :=
{ sup := sup,
  sup_le := λ qc qc' qc'' hqc hqc', begin
    simp [le_iff_forall_get_count_le, sup] at ⊢ hqc hqc',
    intro i,
    by_cases h : qc'.get_count i ≤ qc.get_count i,
    { simpa only [nat.sub_eq_zero_of_le h, zero_add] using hqc i },
    { simpa only [← nat.sub_add_comm (le_of_not_le h),
        nat.add_sub_assoc le_rfl, nat.sub_self, add_zero] using hqc' i }
  end,
  le_sup_left := λ qc qc', by simp [sup, le_iff_forall_get_count_le],
  le_sup_right := λ qc qc', by simp [sup, le_iff_forall_get_count_le, le_tsub_add],
  .. indexed_list.semilattice_inf }

section sup

lemma sup_eq_sub_add : qc ⊔ qc' = (qc' - qc) + qc := rfl

@[simp] lemma sup_apply (i) : (qc ⊔ qc') i =
  list.replicate (max (qc.get_count i) (qc'.get_count i)) () :=
begin
  simp [sup_eq_sub_add, apply_eq_replicate_get_count],
  by_cases h : qc.get_count i ≤ qc'.get_count i,
  { rw [max_eq_right h, ← nat.sub_add_comm h, nat.add_sub_assoc le_rfl, nat.sub_self, add_zero] },
  { rw [max_eq_left (le_of_not_le h), nat.sub_eq_zero_of_le (le_of_not_le h), zero_add] }
end

@[simp] lemma active_oracles_sup : (qc ⊔ qc').active_oracles =
  qc.active_oracles ∪ qc'.active_oracles :=
by simp [finset.ext_iff, mem_active_oracles_iff, list.eq_nil_iff_forall_not_mem, sup_apply,
  list.mem_replicate, or_iff_not_imp_left, -apply_eq_nil]

@[simp] lemma get_count_sup (i) : (qc ⊔ qc').get_count i =
  max (qc.get_count i) (qc'.get_count i) := by simp [get_count_eq_length_apply]

@[simp] lemma sup_empty : qc ⊔ ∅ = qc := sup_bot_eq
@[simp] lemma empty_sup : ∅ ⊔ qc = qc := bot_sup_eq

@[simp] lemma take_at_index_sup (i) (n : ℕ) :
  (qc ⊔ qc').take_at_index i n = qc.take_at_index i n ⊔ qc'.take_at_index i n :=
begin
  refine fun_like.ext _ _ (λ i', _),
  by_cases hi : i = i',
  { induction hi,
    simp [list.take_replicate, min_max_distrib_left, get_count_eq_length_apply] },
  { simp [hi] }
end

end sup

section inf

@[simp] lemma active_oracles_inf : (qc ⊓ qc').active_oracles =
  qc.active_oracles ⊓ qc'.active_oracles :=
begin
  simp only [active_oracles_inf, finset.ext_iff, finset.sep_def, finset.mem_filter,
    finset.inf_eq_inter, finset.mem_inter, and.congr_right_iff, mem_active_oracles_iff_nth_ne_none,
      option.ne_none_iff_exists],
  refine λ i hi, let ⟨u, hu⟩ := hi in ⟨λ h, ⟨u, hu.trans h⟩, λ h, let ⟨u', hu'⟩ := h
    in hu.symm.trans (trans (option.some_inj.2 (punit_eq _ _)) hu')⟩,
end

end inf

@[simp] lemma distjoin_iff_disjoint_active_oracles : disjoint qc qc' ↔
  disjoint qc.active_oracles qc'.active_oracles :=
by simp only [disjoint_iff, bot_eq_empty, eq_empty_iff, active_oracles_inf, finset.bot_eq_empty]

end lattice

instance : has_ordered_sub (query_count spec) :=
{ tsub_le_iff_right := by simp [le_iff_forall_get_count_le],
  .. query_count.has_sub }

section canonically_ordered_add_monoid

instance : canonically_ordered_add_monoid (query_count spec) :=
{ add_le_add_left := λ qc qc' h qc'', by simpa [le_iff_forall_get_count_le] using h,
  le_self_add := indexed_list.le_self_add,
  exists_add_of_le := λ qc qc' hqc, ⟨qc' - qc, query_count.get_count_ext _ _
    (λ i, by simp [← nat.add_sub_assoc (get_count_le_get_count hqc i), nat.add_sub_cancel_left])⟩,
  .. query_count.lattice, .. query_count.add_cancel_comm_monoid,
  .. indexed_list.order_bot }

lemma sup_eq_add (h : disjoint qc qc') : qc ⊔ qc' = qc + qc' :=
begin
  refine fun_like.ext _ _ (λ i, _),
  rw [sup_eq_sub_add, add_apply, sub_apply],
  by_cases hi : i ∈ qc.active_oracles,
  { rw [distjoin_iff_disjoint_active_oracles, disjoint_iff,
      finset.inf_eq_inter, finset.bot_eq_empty] at h,
    have : i ∉ qc'.active_oracles,
    from (λ hi', (finset.not_mem_empty i (h ▸ finset.mem_inter.2 ⟨hi, hi'⟩)).elim),
    simp [apply_eq_nil _ this] },
  { simp [apply_eq_nil _ hi, get_count_eq_zero _ hi] }
end

end canonically_ordered_add_monoid

@[simp] lemma of_nat_le_iff (i n) : of_nat i n ≤ qc ↔ n ≤ qc.get_count i :=
begin
  simp [le_iff_forall_get_count_le, get_count_of_nat],
  refine ⟨λ h, by simpa using h i, λ h i', _⟩,
  by_cases hi : i = i',
  { exact le_of_eq_of_le (if_pos hi) (hi ▸ h) },
  { exact le_of_eq_of_le (if_neg hi) zero_le' }
end

section sep

variables (p q : spec.ι → Prop)

@[simp] lemma sep_or_eq_sup : {x ∈ qc | p x ∨ q x} = {x ∈ qc | p x} ⊔ {x ∈ qc | q x} :=
begin
  haveI : decidable_pred p := classical.dec_pred p,
  haveI : decidable_pred q := classical.dec_pred q,
  ext x,
  sorry, sorry,
  -- by_cases hpx : p x; by_cases hqx : q x; simp only [hpx, hqx, sep_apply', or_self, sup_apply,
  --   max_eq_left, if_true, if_false, true_or, or_true, nat.zero_max, max_comm (qc x)]
end

@[simp] lemma sep_and_eq_inf : {x ∈ qc | p x ∧ q x} = {x ∈ qc | p x} ⊓ {x ∈ qc | q x} :=
begin
  haveI : decidable_pred p := classical.dec_pred p,
  haveI : decidable_pred q := classical.dec_pred q,
  ext x,
  sorry, sorry,
  -- by by_cases hpx : p x; by_cases hqx : q x; simp only [hpx, hqx, sep_apply', and_self, inf_apply,
  --   min_eq_right, zero_min, min_zero, if_true, if_false, and_false, false_and]
end

end sep

end query_count

end oracle_spec