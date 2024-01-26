/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.finset.basic
import data.vector.mem
import data.real.ennreal

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
    },

  }
end


@[simp] lemma vector.nth_cons {n : ℕ} (x : α) (xs : vector α n) (i : fin n.succ) :
  (x ::ᵥ xs).nth i = if hi : i = 0 then x else xs.nth (i.pred hi) :=
begin
  split_ifs with hi,
  { rw [hi, vector.nth_zero, vector.head_cons] },
  {
    obtain ⟨j, rfl⟩ := fin.exists_succ_eq_iff.2 hi,
    rw [vector.nth_cons_succ, fin.pred_succ],
  }
end


lemma list.cons_injective2 {α : Type} : function.injective2 (list.cons : α → list α → list α) :=
begin
  simp [function.injective2, ← and_imp],
  exact λ _ _ _ _, true.intro
end

lemma vector.injective2_cons {α : Type} {n : ℕ} :
  function.injective2 (vector.cons : α → vector α n → vector α (n + 1)) :=
begin
  simp [function.injective2],
  intros x x' xs xs' h,
  refine ⟨_, _⟩,
  { simpa using congr_arg vector.head h },
  { ext m,
    simpa [vector.nth_cons_succ] using congr_arg (λ v, vector.nth v (fin.succ m)) h }
end

lemma prod.mk_injective2 {α β : Type} : function.injective2 (prod.mk : α → β → α × β) :=
λ _ _ _ _, prod.eq_iff_fst_eq_snd_eq.1


example (x y z : ℝ) (hy : 0 ≤ y)
  (hz : x + y = z) : x < z ∨ y = 0 :=
begin
  -- Collapse the equality `x + y = z`
  -- Goal is now `x < x + y ∨ y = 0`
  induction hz,
  -- Seperately consider two cases
  by_cases h : y = 0,
  { exact or.inr h },
  { -- Partially solve the current goal
    -- Two new goals for the `_` holes
    refine or.inl (lt_of_le_of_ne _ _),
    { -- Linear arithmetic solver
      linarith },
    { -- Solve using simplifier
      -- squeeze_simp,
      rwa [ne.def, self_eq_add_right] } }
end


lemma vector.exists_eq_split {m n : ℕ} (v : vector α (n + m)) :
  ∃ v1 : vector α n, ∃ v2 : vector α m, v = v1.append v2 :=
begin
  cases v with xs hxs,
  have hn : n ≤ xs.length := le_of_le_of_eq (le_add_right le_rfl) hxs.symm,
  refine ⟨⟨xs.take n, by simp [hn]⟩, ⟨xs.drop n, by simp [hxs]⟩, _⟩,
  simp [vector.append],
end

-- example (x y z : ℝ) (hy : 0 ≤ y)
--   (hz : x + y = z) : x < z ∨ y = 0 :=
-- by simpa [← hz, @eq_comm _ y] using hy
