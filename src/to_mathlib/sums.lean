/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.general
import probability.probability_mass_function.basic

/-!
# Lemmas about Sums that fit better in mathlib
-/

open_locale nnreal ennreal big_operators

variables {α β γ : Type*}

-- NOTE: not going to PR this
section tsum_prod

open function set

lemma tsum_prod_eq_tsum_snd {α β γ : Type*} [add_comm_monoid α] [topological_space α] [t2_space α]
  {f : β × γ → α} (b : β) (h : ∀ c, ∀ b' ≠ b, f (b', c) = 0) :
  ∑' (x : β × γ), f x = ∑' (c : γ), f (b, c) :=
begin
  have : support f ⊆ range (λ x, (b, x)),
  { rintros ⟨b, c'⟩ hx, obtain rfl := of_not_not ((h _ _).mt hx.out), exact mem_range_self _ },
  rw [← tsum_subtype_eq_of_support_subset this, tsum_range f (prod.mk.inj_left b)]
end

lemma tsum_prod_eq_tsum_fst {α β γ : Type*} [add_comm_monoid α] [topological_space α] [t2_space α]
  {f : β × γ → α} (c : γ) (h : ∀ b, ∀ c' ≠ c, f (b, c') = 0) :
  ∑' (x : β × γ), f x = ∑' (b : β), f (b, c) :=
begin
  have : support f ⊆ range (λ x, (x, c)),
  { rintros ⟨b, c'⟩ hx, obtain rfl := of_not_not ((h _ _).mt hx.out), exact mem_range_self _ },
  rw [← tsum_subtype_eq_of_support_subset this, tsum_range f (prod.mk.inj_right c)]
end

end tsum_prod

section option

-- TODO: wasn't this merged somewhere?
lemma tsum_option_eq_extract_none {α β : Type*} [add_comm_group α] [topological_space α]
  [topological_add_group α] [t2_space α] [decidable_eq β]
  (f : option β → α) (hf : summable f) : tsum f = f none + ∑' x, f (some x) :=
begin
  have := (tsum_eq_add_tsum_ite hf none),
  refine trans this (congr_arg ((+) (f none)) _),
  sorry,

  -- refine (tsum_eq_tsum_of_ne_zero_bij (λ a, some a.1) _ (λ x hx, _) _),
  -- refine congr_arg (λ x, f none + x) _,
end

lemma ennreal.tsum_option (f : option α → ℝ≥0∞) :
  tsum f = f none + ∑' a, f (some a) :=
begin
  refine trans (ennreal.tsum_eq_add_tsum_ite none) _,
  refine congr_arg (λ x, f none + x) _,
  refine (tsum_eq_tsum_of_ne_zero_bij (λ a, some a.1) _ (λ x hx, _) _),
  { simp only [subtype.val_eq_coe, imp_self, set_coe.forall, implies_true_iff] },
  { rw [function.mem_support, ne.def, ite_eq_left_iff, not_imp,
      ← ne.def, option.ne_none_iff_exists] at hx,
    obtain ⟨y, hy⟩ := hx.1,
    refine set.mem_range.2 ⟨⟨y, function.mem_support.2 (hy.symm ▸ hx.2)⟩, hy⟩ },
  convert λ x, if_neg (option.some_ne_none _),
end

lemma nnreal.tsum_option [decidable_eq α] {f : option α → ℝ≥0} (hf : summable f) :
  tsum f = f none + ∑' (a : α), f (some a) :=
calc ∑' (x : option α), f x
  = f none + ∑' (x : option α), ite (x = none) 0 (f x) :
  begin
    convert @nnreal.tsum_eq_add_tsum_ite (option α) f hf none,
    ext x, split_ifs,
    refl, refl,
  end
  ... = f none + ∑' (a : α), f (some a) : begin
    refine congr_arg (λ x, f none + x) (tsum_eq_tsum_of_ne_zero_bij (λ a, some a.1) _ _ _),
    { simp only [subtype.val_eq_coe, imp_self, set_coe.forall, implies_true_iff] },
    { simp only [function.support_subset_iff, ne.def, ite_eq_left_iff, not_forall, exists_prop,
        set.mem_range, set_coe.exists, function.mem_support, and_imp],
      intros x hx hfx,
      cases x with a,
      { exact false.elim (hx rfl) },
      { exact ⟨a, hfx, rfl⟩ } },
    { simp only [subtype.val_eq_coe, if_false, eq_self_iff_true, implies_true_iff] }
end

theorem dedup_eq_cons_iff [decidable_eq α] (l : list α) (a : α) (l' : list α) :
  l.dedup = a :: l' ↔ a ∈ l ∧ a ∉ l' ∧ l' = l.dedup.tail :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { refine ⟨list.mem_dedup.1 (h.symm ▸ list.mem_cons_self _ _), λ ha, _, by rw [h, list.tail_cons]⟩,
    have : list.count a l.dedup ≤ 1 := list.nodup_iff_count_le_one.1 (list.nodup_dedup l) a,
    rw [h, list.count_cons_self, add_le_iff_nonpos_left] at this,
    exact (not_le_of_lt (list.count_pos.2 ha) this) },
  { obtain ⟨ha, ha', h⟩ := h,
    have := @list.cons_head_tail α ⟨a⟩ _ (list.ne_nil_of_mem (list.mem_dedup.2 ha)),
    have hal : a ∈ l.dedup := list.mem_dedup.2 ha,
    rw [← this, ← h, list.cons_eq_cons],
    rw [← this, list.mem_cons_iff, or_iff_not_imp_right] at hal,
    refine ⟨(hal (h ▸ ha')).symm, rfl⟩ }
end


theorem head_dedup [decidable_eq α] [inhabited α] (l : list α) :
  l.dedup.head = if l.head ∈ l.tail then l.tail.dedup.head else l.head :=
match l with
| [] := rfl
| (a :: l) := by { by_cases ha : a ∈ l; simp [ha, list.dedup_cons_of_mem] }
end

theorem tail_dedup [decidable_eq α] [inhabited α] (l : list α) :
  l.dedup.tail = if l.head ∈ l.tail then l.tail.dedup.tail else l.tail.dedup :=
match l with
| [] := rfl
| (a :: l) := by { by_cases ha : a ∈ l; simp [ha, list.dedup_cons_of_mem] }
end

end option