/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.finset.basic
import data.vector.mem

/-!
# Misc Lemmas That Ideally Should Port to Mathlib
-/

variables {α β γ : Type*}

@[simp] lemma finset.count_to_list [decidable_eq α] (s : finset α) (x : α) :
  s.to_list.count x = ite (x ∈ s) 1 0 :=
by simp_rw [list.count_eq_of_nodup s.nodup_to_list, finset.mem_to_list]

@[simp] lemma list.tail_eq_nil (xs : list α) : xs.tail = [] ↔ xs = [] :=
begin
  sorry,
end

lemma list.eq_iff_head_eq_tail_eq [inhabited α] (xs ys : list α) :
  xs = ys ↔ (xs.head = ys.head ∧ xs.tail = ys.tail):=
begin
  refine ⟨λ h, by simp [h], λ h, _⟩,
  {
    cases ys with y ys,
    {
      refine xs.tail_eq_nil.1 h.2
    },
    {
      cases xs with x xs,
      {
        refine false.elim _,
      },
      {
        simp at h,
        simp [h.1, h.2]
      }
    }
  }
end