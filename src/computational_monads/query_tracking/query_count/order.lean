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
@[simp] lemma add_empty : ∅ + qc = qc := zero_add qc
@[simp] lemma empty_add : qc + ∅ = qc := add_zero qc

lemma zero_eq_empty : (0 : query_count spec) = ∅ := rfl
@[simp] lemma zero_apply (i) : (0 : query_count spec) i = 0 := rfl
@[simp] lemma active_oracles_zero : (0 : query_count spec).active_oracles = ∅ := rfl

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

section sep

variables (p q : spec.ι → Prop)

lemma sep_or_eq_sup : {x ∈ qc | p x ∨ q x} = {x ∈ qc | p x} ⊔ {x ∈ qc | q x} :=
begin
  haveI : decidable_pred p := classical.dec_pred p,
  haveI : decidable_pred q := classical.dec_pred q,
  ext x,
  by_cases hpx : p x; by_cases hqx : q x; simp only [hpx, hqx, sep_apply', or_self, sup_apply,
    max_eq_left, if_true, if_false, true_or, or_true, nat.zero_max, max_comm (qc x)]
end

lemma sep_and_eq_inf : {x ∈ qc | p x ∧ q x} = {x ∈ qc | p x} ⊓ {x ∈ qc | q x} :=
begin
  haveI : decidable_pred p := classical.dec_pred p,
  haveI : decidable_pred q := classical.dec_pred q,
  ext x,
  by by_cases hpx : p x; by_cases hqx : q x; simp only [hpx, hqx, sep_apply', and_self, inf_apply,
    min_eq_right, zero_min, min_zero, if_true, if_false, and_false, false_and]
end

end sep

section list_sum

lemma list_sum_apply (qcs : list (query_count spec)) (i : spec.ι) :
  qcs.sum i = (qcs.map (λ (qc : query_count spec), qc i)).sum :=
begin
  induction qcs with qc qcs hqcs,
  { simp },
  { simp [hqcs] }
end

lemma active_oracles_list_sum (qcs : list (query_count spec)) :
  qcs.sum.active_oracles = (list.foldr (∪) ∅ (qcs.map active_oracles)) :=
begin
  sorry,
end


end list_sum

section sum_of_list

def sum_of_list (qc : query_count spec) (js : list spec.ι) : query_count spec :=
(js.map (λ i, of_nat i (qc i))).sum

variables (j : spec.ι) (js : list spec.ι)

@[simp] lemma sum_of_list_nil : qc.sum_of_list [] = ∅ := rfl

@[simp] lemma sum_of_list_cons : qc.sum_of_list (j :: js) =
  of_nat j (qc j) + qc.sum_of_list js := by simp only [sum_of_list, list.map, list.sum_cons]

lemma sum_of_list_apply (i) : (qc.sum_of_list js) i = js.count i * qc i :=
begin
  induction js with j js hjs,
  { simp only [sum_of_list_nil, empty_apply, list.count_nil, zero_mul] },
  { by_cases hi : i = j,
    { induction hi,
      simp [hjs, add_mul] },
    { simp [hi, ne.symm hi, hjs] } }
end

lemma active_oracles_sum_of_list : (qc.sum_of_list js).active_oracles =
  qc.active_oracles.filter (λ i, i ∈ js) :=
begin
  ext i,
  simp [sum_of_list],
  sorry,
end

end sum_of_list

end query_count

end oracle_comp