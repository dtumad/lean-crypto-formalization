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

open_locale ennreal

lemma finset.count_to_list [decidable_eq α] (s : finset α) (a : α) :
  s.to_list.count a = ite (a ∈ s) 1 0 :=
by simp only [list.count_eq_of_nodup s.nodup_to_list, finset.mem_to_list]

lemma vector.cons_eq_cons {n : ℕ} (x y : α) (xs ys : vector α n) :
  x ::ᵥ xs = y ::ᵥ ys ↔ x = y ∧ xs = ys :=
⟨λ h, have x = y ∧ xs.to_list = ys.to_list, by simpa only [vector.to_list_cons]
  using congr_arg vector.to_list h, ⟨this.1, vector.eq _ _ this.2⟩, λ h, h.1 ▸ h.2 ▸ rfl⟩

-- lemma vector.zip_with_comp {n : ℕ} (f : α → β) (g : β → γ) (v : vector α n) :
