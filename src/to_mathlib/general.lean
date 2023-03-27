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

section add

lemma list.repeat_add (x : α) (m n : ℕ) :
  list.repeat x (n + m) = list.repeat x n ++ list.repeat x m :=
begin
  induction n with n hn,
  { rw [list.repeat, zero_add, list.nil_append] },
  { rw [nat.succ_add, list.repeat, hn, ← list.cons_append, list.repeat] }
end

end add

section mem

/-- Only `x` is a member of `list.repeat x n` (unless `n = 0` which has no members). -/
@[simp] lemma list.mem_repeat_iff (y : α) : y ∈ (list.repeat x n) ↔ 0 < n ∧ y = x :=
begin
  induction n with n hn,
  { rw [lt_self_iff_false, false_and, list.repeat, list.mem_nil_iff] },
  { simp [hn] }
end

lemma list.not_mem_repeat_zero (y : α) : y ∉ (list.repeat x 0) :=
by simp_rw [list.mem_repeat_iff, lt_self_iff_false, false_and, not_false_iff]

lemma list.mem_repeat_succ_iff (y : α) : y ∈ (list.repeat x n.succ) ↔ y = x :=
by simp_rw [list.mem_repeat_iff, nat.zero_lt_succ, true_and]

lemma list.eq_of_mem_repeat {x y : α} {n : ℕ} (hy : y ∈ (list.repeat x n)) : y = x :=
((list.mem_repeat_iff x n y).1 hy).2

lemma list.pos_of_mem_repeat {x y : α} {n : ℕ} (hy : y ∈ (list.repeat x n)) : 0 < n :=
((list.mem_repeat_iff x n y).1 hy).1

end mem

section nth

@[simp] lemma list.nth_le_repeat (m : ℕ) (hm : m < (list.repeat x n).length) :
  (list.repeat x n).nth_le m hm = x :=
list.eq_of_mem_repeat (list.mem_iff_nth_le.2 ⟨m, hm, rfl⟩)

@[simp] lemma list.nth_repeat (m : ℕ) : (list.repeat x n).nth m = if m < n then some x else none :=
begin
  split_ifs with h,
  { exact list.nth_eq_some.2 ⟨(list.length_repeat x n).symm ▸ h, list.nth_le_repeat x n m _⟩ },
  { exact list.nth_eq_none_iff.2 (le_of_not_lt $ (list.length_repeat x n).symm ▸ h) }
end

lemma list.nth_repeat_eq_none_iff (m : ℕ) : (list.repeat x n).nth m = none ↔ n ≤ m :=
by rw [list.nth_eq_none_iff, list.length_repeat]

lemma list.nth_repeat_eq_some_iff (m : ℕ) (y : α) :
  (list.repeat x n).nth m = some y ↔ m < n ∧ x = y :=
by simp only [ite_eq_iff, list.nth_repeat, and_false, or_false]

end nth

section find

lemma list.find_repeat (p : α → Prop) [decidable_pred p] :
  (list.repeat x n).find p = if 0 < n ∧ p x then some x else none :=
begin
  split_ifs with hx,
  { cases n with n,
    { exact ((lt_self_iff_false 0).1 hx.1).elim },
    { exact list.find_cons_of_pos _ hx.2 } },
  { refine list.find_eq_none.2 (λ y hy, (list.eq_of_mem_repeat hy).symm ▸ _),
    simpa only [not_and_distrib, list.pos_of_mem_repeat hy, not_true, false_or] using hx }
end

@[simp] lemma list.find_repeat_eq_none_iff  (p : α → Prop) [decidable_pred p] :
  (list.repeat x n).find p = none ↔ n = 0 ∨ ¬ p x :=
by simp_rw [list.find_repeat, ite_eq_right_iff, imp_false, not_and_distrib, not_lt, le_zero_iff]

@[simp] lemma list.find_repeat_eq_some_iff (p : α → Prop) [decidable_pred p] (y : α) :
  (list.repeat x n).find p = some y ↔ 0 < n ∧ p x ∧ y = x :=
by simp_rw [list.find_repeat, ite_eq_iff, and_assoc, eq_comm, and_false, or_false]

end find

section all

@[simp] lemma list.all₂_repeat_iff (p : α → Prop) : (list.repeat x n).all₂ p ↔ n = 0 ∨ p x :=
by simp [list.all₂_iff_forall, lt_iff_not_le, or_iff_not_imp_left]

@[simp] lemma list.all_repeat (p : α → bool) :
  (list.repeat x n).all p = if n = 0 then tt else p x :=
begin
  induction n with n hn,
  { refl },
  {
    rw [list.repeat, list.all, list.foldr_cons],
    rw [list.all] at hn,
    rw [hn],
    simp,
    split_ifs,
    simp,
    simp,

  }
end

end all

section reverse

-- lemma list.reverse_repeat

end reverse

section map

lemma list.map_repeat (f : α → β) : (list.repeat x n).map f = list.repeat (f x) n :=
begin
  induction n with n hn,
  { refl },
  { refine (list.map_cons f x _).trans (congr_arg ((::) (f x)) hn) }
end

end map

end list_stuff