/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.basic

/-!
# Ordering on Query Counts

This file defines an order on `query_count`, where `qc ≤ qc'` iff the count at each index
is smaller in `qc` than in `qc'`. Note this is only a partial order.

We also define ordered addition and subtraction operations by piecewise addition and subtraction.
-/

namespace oracle_comp

open oracle_spec

namespace query_count

variables {α β γ : Type} {spec : oracle_spec} (qc qc' : query_count spec)

section lattice

protected def inf (qc qc' : query_count spec) : query_count spec :=
{ get_count := λ i, min (qc i) (qc' i),
  active_oracles := qc.active_oracles ∩ qc'.active_oracles,
  mem_active_oracles_iff' := by simp [not_or_distrib] }

protected def sup (qc qc' : query_count spec) : query_count spec :=
{ get_count := λ i, max (qc i) (qc' i),
  active_oracles := qc.active_oracles ∪ qc'.active_oracles,
  mem_active_oracles_iff' := by simp [or_iff_not_imp_left] }

instance : lattice (query_count spec) :=
{ le := λ qc qc', ∀ (i : spec.ι), qc i ≤ qc' i,
  le_refl := λ qc i, le_rfl,
  le_trans := λ qc qc' qc'' h h' i, (h i).trans (h' i),
  le_antisymm := λ qc qc' h h', fun_like.ext qc qc' (λ i, le_antisymm (h i) (h' i)),
  inf := query_count.inf,
  le_inf := λ qc qc' qc'' h h' i, le_min (h i) (h' i),
  inf_le_left := λ qc qc' i, min_le_left _ _,
  inf_le_right := λ qc qc' i, min_le_right _ _,
  sup := query_count.sup,
  sup_le := λ qc qc' qc'' h h' i, max_le (h i) (h' i),
  le_sup_left := λ qc qc' i, le_max_left _ _,
  le_sup_right := λ qc qc' i, le_max_right _ _ }

lemma le_iff_forall : qc ≤ qc' ↔ ∀ i, qc i ≤ qc' i := iff.rfl

@[simp] lemma inf_apply (i) : (qc ⊓ qc') i = min (qc i) (qc' i) := rfl
@[simp] lemma active_oracles_inf : (qc ⊓ qc').active_oracles =
  qc.active_oracles ∩ qc'.active_oracles := rfl

@[simp] lemma sup_apply (i) : (qc ⊔ qc') i = max (qc i) (qc' i) := rfl
@[simp] lemma active_oracles_sup : (qc ⊔ qc').active_oracles =
  qc.active_oracles ∪ qc'.active_oracles := rfl

end lattice

section canonically_ordered_add_monoid

protected def add (qc qc' : query_count spec) : query_count spec :=
{ get_count := λ i, qc i + qc' i,
  active_oracles := qc.active_oracles ∪ qc'.active_oracles,
  mem_active_oracles_iff' := by simp [or_iff_not_imp_left] }

protected noncomputable def sub (qc qc' : query_count spec) : query_count spec :=
{ get_count := λ i, qc i - qc' i,
  active_oracles := {i ∈ qc.active_oracles | qc' i < qc i},
  mem_active_oracles_iff' := by { simp, exact λ i' h, mem_active_oracles _ (ne_zero_of_lt h) } }

instance : canonically_ordered_add_monoid (query_count spec) :=
{ add := query_count.add,
  zero := ∅, bot := ∅,
  bot_le := λ qc i, zero_le',
  add_comm := λ qc qc', fun_like.ext _ _ (λ i, add_comm (qc i) (qc' i)),
  add_assoc := λ qc qc' qc'', fun_like.ext _ _ (λ i, add_assoc (qc i) (qc' i) (qc'' i)),
  add_zero := λ qc, fun_like.ext _ _ (λ i, add_zero (qc i)),
  zero_add := λ qc, fun_like.ext _ _ (λ i, zero_add (qc i)),
  add_le_add_left := λ qc qc' h qc₀ i, add_le_add_left (h i) (qc₀ i),
  exists_add_of_le := λ qc qc' h, ⟨qc'.sub qc, fun_like.ext _ _
    (λ i, trans (nat.add_sub_cancel_left _ _).symm (nat.add_sub_assoc (h i) _))⟩,
  le_self_add := λ qc qc' i, le_self_add,
  ..query_count.lattice}

@[simp] lemma empty_le : ∅ ≤ qc := bot_le
@[simp] lemma inf_empty : qc ⊓ ∅ = ∅ := inf_bot_eq
@[simp] lemma empty_inf : ∅ ⊓ qc = ∅ := bot_inf_eq
@[simp] lemma sup_empty : qc ⊔ ∅ = qc := sup_bot_eq
@[simp] lemma empty_sup : ∅ ⊔ qc = qc := bot_sup_eq
lemma zero_eq_empty : (0 : query_count spec) = ∅ := rfl

@[simp] lemma add_apply (i) : (qc + qc') i = qc i + qc' i := rfl
@[simp] lemma active_oracles_add : (qc + qc').active_oracles =
  qc.active_oracles ∪ qc'.active_oracles := rfl

end canonically_ordered_add_monoid

section has_ordered_sub

noncomputable instance : has_sub (query_count spec) :=
{ sub := query_count.sub }

@[simp] lemma sub_apply (i) : (qc - qc') i = qc i - qc' i := rfl
@[simp] lemma active_oracles_sub : (qc - qc').active_oracles =
  {i ∈ qc.active_oracles | qc' i < qc i} := rfl

instance : has_ordered_sub (query_count spec) :=
{ tsub_le_iff_right := by simp [le_iff_forall] }

end has_ordered_sub

section of_nat

@[simp] lemma of_nat_le_iff (i : spec.ι) (n) : of_nat i n ≤ qc ↔ n ≤ qc i :=
begin
  refine ⟨λ h, le_of_eq_of_le (of_nat_apply_self i n).symm (h i), λ h i', _⟩,
  by_cases hi : i = i',
  { induction hi, simpa },
  { simp [hi] }
end

@[simp] lemma add_of_nat (i : spec.ι) (n) : qc + of_nat i n = qc.increment i n :=
by simp [fun_like.ext_iff, add_ite]

@[simp] lemma of_nat_add (i : spec.ι) (n) : of_nat i n + qc = qc.increment i n :=
by rw [add_comm, add_of_nat]

@[simp] lemma sub_of_nat (i : spec.ι) (n) : qc - of_nat i n = qc.decrement i n :=
fun_like.ext _ _ (λ i', by by_cases hi : i = i'; simp [hi])

end of_nat

end query_count

end oracle_comp