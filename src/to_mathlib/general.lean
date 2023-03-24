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

section list_stuff

variables (x : α) (n : ℕ)

@[simp] lemma list.mem_repeat_iff (y : α) : y ∈ (list.repeat x n) ↔ n ≠ 0 ∧ y = x :=
begin
  induction n with n hn,
  { rw [list.repeat, list.mem_nil_iff, ne.def, ne_self_iff_false, false_and] },
  { simp only [hn, list.repeat, list.mem_cons_iff, ne.def, nat.succ_ne_zero, not_false_iff,
      true_and, or_iff_left_iff_imp, and_imp, imp_self, implies_true_iff] }
end

lemma list.not_mem_repeat_zero (y : α) : y ∉ (list.repeat x 0) :=
by simp only [list.mem_repeat_iff, ne.def, ne_self_iff_false, false_and, not_false_iff]

lemma list.mem_repeat_succ_iff (y : α) : y ∈ (list.repeat x n.succ) ↔ y = x :=
by simp only [list.mem_repeat_iff, ne.def, nat.succ_ne_zero, not_false_iff, true_and]

lemma list.eq_of_mem_repeat {x y : α} {n : ℕ} (hy : y ∈ (list.repeat x n)) : y = x :=
sorry

@[simp] lemma list.nth_repeat_eq_none_iff (m : ℕ) : (list.repeat x n).nth m = none ↔ n < m :=
sorry

@[simp] lemma list.nth_repeat_eq_some_iff (m : ℕ) (y : α) :
  (list.repeat x n).nth m = some y ↔ m ≤ n ∧ y = x :=
sorry

lemma list.nth_repeat (m : ℕ) : (list.repeat x n).nth m = if m ≤ n then some x else none :=
sorry

@[simp] lemma list.find_repeat_eq_none_iff  (p : α → Prop) [decidable_pred p] :
  (list.repeat x n).find p = none ↔ n = 0 ∨ ¬ p x :=
sorry

@[simp] lemma list.find_repeat_eq_some_iff (p : α → Prop) [decidable_pred p] (y : α) :
  (list.repeat x n).find p = some y ↔ 0 < n ∧ p x ∧ y = x :=
sorry

lemma list.find_repeat (p : α → Prop) [decidable_pred p] :
  (list.repeat x n).find p = if p x then some x else none :=
begin
  sorry
end

end list_stuff

lemma vector.mem_repeat_succ (n : ℕ) (x y : α) :
  y ∈ (vector.repeat x n.succ).to_list ↔ y = x :=
begin
  rw [vector.repeat, vector.to_list],
  simp [list.repeat],
  -- sorry
end

-- lemma vector.zip_with_comp {n : ℕ} (f : α → β) (g : β → γ) (v : vector α n) :
