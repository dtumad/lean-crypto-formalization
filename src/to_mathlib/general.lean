/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import probability.probability_mass_function.basic

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

variables {α β γ : Type*}

lemma finset.count_to_list [decidable_eq α] (s : finset α) (a : α) :
  s.to_list.count a = ite (a ∈ s) 1 0 :=
by simp only [list.count_eq_of_nodup s.nodup_to_list, finset.mem_to_list]

lemma finset.coe_eq_coe_iff (s s' : finset α) : (s : set α) = (s' : set α) ↔ s = s' :=
begin
  refine ⟨λ h, finset.ext (λ x, _), λ h, congr_arg coe h⟩,
  rw [← finset.mem_coe, ← finset.mem_coe, h],
end