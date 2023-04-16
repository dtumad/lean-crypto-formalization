/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.finset.basic

/-!
# Misc Lemmas That Ideally Should Port to Mathlib
-/

variables {α β γ : Type*}

@[simp] lemma finset.count_to_list [decidable_eq α] (s : finset α) (x : α) :
  s.to_list.count x = ite (x ∈ s) 1 0 :=
by simp_rw [list.count_eq_of_nodup s.nodup_to_list, finset.mem_to_list]