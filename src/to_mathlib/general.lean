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

lemma nat_helper_thing {a b c : ℕ} (h : a ≤ b) :
  c + a - b = c - (b - a) :=
begin
  induction c with c hc,
  {
    simpa,
  },
  {
    by_cases h' : b ≤ c + a,
    {
      rw [nat.succ_add],
      rw [nat.succ_sub h'],
      rw [hc],
      rw [← nat.succ_sub (tsub_le_iff_right.2 h')],
    },
    {
      rw [not_le] at h',
      have : c.succ + a - b = 0 := begin
        rwa [nat.sub_eq_zero_iff_le, nat.succ_add, nat.succ_le_iff],
      end,
      rwa [this, eq_comm, nat.sub_eq_zero_iff_le, nat.le_sub_iff_right h, nat.succ_add,
        nat.succ_le_iff],
    }


  }
end