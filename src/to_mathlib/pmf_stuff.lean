/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.sums
import probability.probability_mass_function.uniform

/-!
# Lemmas about probability mass functions to move to mathlib
-/

open_locale measure_theory nnreal ennreal big_operators classical
open measure_theory

variables {α β γ : Type*}

section monad

lemma pmf.pure_eq_iff (a : α) (p : pmf α) : pmf.pure a = p ↔ ∀ x ≠ a, p x = 0 :=
(pmf.ext_iff).trans ⟨λ h x hx, (h x).symm.trans (if_neg hx), λ h x, ite_eq_iff'.2 ⟨λ hxa,
  p.tsum_coe.symm.trans (tsum_eq_single x (λ y hy, h y (hxa ▸ hy))), λ hxa, symm $ h x hxa⟩⟩

lemma pmf.eq_pure_iff (a : α) (p : pmf α) : p = pmf.pure a ↔ ∀ x ≠ a, p x = 0 :=
by rw [@eq_comm _ p, pmf.pure_eq_iff]

@[simp] lemma pmf.map_pure {α β : Type*} (f : α → β) (a : α) :
  (pmf.pure a).map f = pmf.pure (f a) := pmf.pure_map _ _

lemma pmf.bind_apply_eq_one_iff {α β : Type*} (p : pmf α) (q : α → pmf β) (y : β) :
  (p.bind q) y = 1 ↔ ∀ x ∈ p.support, (q x).support ⊆ {y} :=
begin
  rw [pmf.apply_eq_one_iff, pmf.support_bind],
  refine ⟨λ h x hx y' hy', _, λ h, set.subset.antisymm _ _⟩,
  {
    rw ← h,
    simp only [set.mem_Union],
    refine ⟨x, hx, hy'⟩,
  },
  {
    rintro y' ⟨s, ⟨x, hx⟩, hs⟩,
    simp only [] at hx,
    rw ← hx at hs,
    simp only [set.mem_Union] at hs,
    obtain ⟨hx, hx'⟩ := hs,
    refine h x hx hx',
  },
  {
    intros y' hy',
    rw [set.mem_singleton_iff] at hy',

    obtain ⟨rfl⟩ := hy',
    clear hy',
    simp only [set.mem_Union],
    obtain ⟨x, hx⟩ := p.support_nonempty,
    obtain ⟨y', hy'⟩ := (q x).support_nonempty,
    specialize h x hx hy',
    refine ⟨x, hx, _⟩,
    rw [set.mem_singleton_iff] at h,
    refine h ▸ hy'
  }
end

end monad

section union

lemma pmf.measurable_set_to_outer_measure_caratheodory (p : pmf α) (s : set α) :
  measurable_set[p.to_outer_measure.caratheodory] s :=
p.to_outer_measure_caratheodory.symm ▸ measurable_space.measurable_set_top

lemma pmf.to_measure_apply_Union {α : Type*} [measurable_space α] (p : pmf α)
  {f : ℕ → set α} (hf : ∀ n, measurable_set (f n)) (h : pairwise (disjoint on f)) :
  p.to_measure (⋃ n, f n) = ∑' n, p.to_measure (f n) :=
p.to_measure.m_Union hf h

lemma pmf.to_measure_apply_union {α : Type*} [measurable_space α] (p : pmf α)
  {s t : set α} (ht : measurable_set t) (h : disjoint s t) :
  p.to_measure (s ∪ t) = p.to_measure s + p.to_measure t :=
measure_theory.measure_union h ht

lemma pmf.to_outer_measure_apply_Union {α : Type*} (p : pmf α) {f : ℕ → set α}
  (h : pairwise (disjoint on f)) : p.to_outer_measure (⋃ n, f n) = ∑' n, p.to_outer_measure (f n) :=
measure_theory.outer_measure.Union_eq_of_caratheodory _
  (λ n, pmf.measurable_set_to_outer_measure_caratheodory _ (f n)) h

lemma pmf.to_outer_measure_apply_union {α : Type*} (p : pmf α) {s t : set α}
  (h : disjoint s t) : p.to_outer_measure (s ∪ t) = p.to_outer_measure s + p.to_outer_measure t :=
begin
  sorry
end

lemma pmf.to_measure_apply_union_add_inter [measurable_space α]
  (p : pmf α) (s t : set α) (h : measurable_set t) :
  p.to_measure (s ∪ t) + p.to_measure (s ∩ t) = p.to_measure s + p.to_measure t :=
measure_theory.measure_union_add_inter s h

lemma pmf.to_outer_measure_apply_union_add_inter (p : pmf α) (s t : set α) :
  p.to_outer_measure (s ∪ t) + p.to_outer_measure (s ∩ t) =
    p.to_outer_measure s + p.to_outer_measure t :=
begin
  sorry
end

end union

section prod

/-- If and intermediate distribution is a product, can express the probability as a
double sum rather than a sum over a `prod` type. -/
lemma pmf.prod_bind_apply {α β γ : Type*}
  (p : pmf (α × β)) (q : α × β → pmf γ) (c : γ) :
  p.bind q c = ∑' (a : α) (b : β), p (a, b) * q (a, b) c :=
tsum_prod' ennreal.summable $ λ _, ennreal.summable

lemma pmf.prod_bind_apply' {α β γ : Type*}
  (p : pmf (α × β)) (q : α × β → pmf γ) (c : γ) :
  p.bind q c = ∑' (b : β) (a : α), p (a, b) * q (a, b) c :=
(pmf.prod_bind_apply p q c).trans (by rw ennreal.tsum_comm)

/-- First output of a computation of a `prod` type as a summation over possible second outputs. -/
lemma pmf.map_fst_apply {α β : Type*} (p : pmf (α × β)) (a : α) :
  p.map prod.fst a = ∑' (b : β), p (a, b) :=
calc p.map prod.fst a = ∑' (a' : α) (b : β), ite (a = a') (p (a', b)) 0 :
    by simp_rw [pmf.map, pmf.prod_bind_apply p, function.comp_apply,
      pmf.pure_apply, mul_ite, mul_one, mul_zero]
  ... = ∑' (b : β), ite (a = a) (p (a, b)) 0 :
    tsum_eq_single _ (λ a' ha', by simp only [ne.symm ha', if_false, tsum_zero])
  ... = ∑' (b : β), p (a, b) : by simp only [eq_self_iff_true, if_true]

/-- Second output of a computation of a `prod` type as a summation over possible first outputs. -/
lemma pmf.map_snd_apply {α β : Type*} (p : pmf (α × β)) (b : β) :
  p.map prod.snd b = ∑' (a : α), p (a, b) :=
calc p.map prod.snd b = ∑' (b' : β) (a : α), ite (b = b') (p (a, b')) 0 :
    by simp_rw [pmf.map, pmf.prod_bind_apply' p, function.comp_apply,
      pmf.pure_apply, mul_ite, mul_one, mul_zero]
  ... = ∑' (a : α), ite (b = b) (p (a, b)) 0 :
    tsum_eq_single _ (λ a' ha', by simp only [ne.symm ha', if_false, tsum_zero])
  ... = ∑' (a : α), p (a, b) : by simp only [eq_self_iff_true, if_true]

end prod

section outer_measure

lemma pmf.to_outer_measure_apply_insert (p : pmf α) (x : α) (s : set α) :
  p.to_outer_measure (insert x s) = p x + p.to_outer_measure (s \ {x}) :=
begin
  rw [← set.union_singleton], sorry
  -- rw [pmf.to_outer_measure_apply_Union]
end

lemma pmf.to_outer_measure_apply_diff (p : pmf α) (s t : set α) :
  p.to_outer_measure (s \ t) = p.to_outer_measure s - p.to_outer_measure (s ∩ t) :=
sorry

end outer_measure