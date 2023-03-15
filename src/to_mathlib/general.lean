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

lemma list.not_mem_repeat_zero (x y : α) :
  y ∉ (list.repeat x 0) := by simp only [list.repeat, list.not_mem_nil, not_false_iff]

lemma list.mem_repeat_succ (n : ℕ) (x y : α) :
  y ∈ (list.repeat x n.succ) ↔ y = x :=
begin
  sorry
end

lemma list.eq_of_mem_repeat {n : ℕ} {x y : α} (hy : y ∈ list.repeat x n) : y = x :=
begin
  cases n with n,
  { exact false.elim (list.not_mem_repeat_zero x y hy) },
  { exact (list.mem_repeat_succ n x y).1 hy }
end

lemma vector.mem_repeat_succ (n : ℕ) (x y : α) :
  y ∈ (vector.repeat x n.succ).to_list ↔ y = x :=
begin
  rw [vector.repeat, vector.to_list],
  simp [list.repeat],
  sorry
end

-- lemma vector.zip_with_comp {n : ℕ} (f : α → β) (g : β → γ) (v : vector α n) :
