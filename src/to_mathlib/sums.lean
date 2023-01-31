/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.general
import topology.algebra.infinite_sum

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

end option

section vector

lemma tsum_vector_succ [add_comm_monoid β] [topological_space β]
  (n : ℕ) (f : vector α n.succ → β) :
  ∑' (xs' : vector α n.succ), f xs' = ∑' (x : α) (xs : vector α n), f (x ::ᵥ xs) :=
begin
  sorry
end

end vector