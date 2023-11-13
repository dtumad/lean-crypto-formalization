/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.general
import probability.probability_mass_function.basic
import measure_theory.integral.mean_inequalities

/-!
# Lemmas about Sums that fit better in mathlib
-/

open_locale nnreal ennreal big_operators classical

variables {α β γ : Type*}

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

end option

section jensen


theorem ennreal.pow_sum_div_card_le_sum_pow (s : finset α) (f : α → ℝ≥0∞)
  (hf : ∀ x ∈ s, f x ≠ ∞) (n : ℕ) :
  (∑ x in s, f x) ^ (n + 1) / ↑(s.card) ^ n ≤ ∑ x in s, f x ^ (n + 1) :=
begin
  have := nnreal.pow_sum_div_card_le_sum_pow s (λ x, (f x).to_nnreal) n,
  rw [← ennreal.to_nnreal_le_to_nnreal],
  refine le_trans _ (le_trans this _),
  {

    rw [ennreal.to_nnreal_div, ennreal.to_nnreal_pow,
      ennreal.to_nnreal_pow, ennreal.to_nnreal_sum,
      ennreal.to_nnreal_nat],
    exact hf,
  },
  {
    rw [ennreal.to_nnreal_sum],
    simp only [ennreal.to_nnreal_pow],
    intros x hx,
    specialize hf x hx,
    simpa,
  },
  {
    rw [ne.def, ennreal.div_eq_top],
    simp [not_or_distrib],
    refine ⟨λ x hx hx', _, _⟩,
    rw [pow_eq_zero_iff', nat.cast_eq_zero],
    simp [finset.card_ne_zero_of_mem hx],

    refine ne_top_of_lt (ennreal.sum_lt_top hf),
  },
  {
    refine ne_top_of_lt (ennreal.sum_lt_top (λ x hx, _)),
    refine ennreal.pow_ne_top (hf x hx),
  }
end

lemma ennreal.pow_two_sum_le_sum_pow_two (s : finset α) (f : α → ℝ≥0∞)
  (hf : ∀ x ∈ s, f x ≠ ∞) :
  (∑ x in s, f x) ^ 2 ≤ ∑ x in s, s.card * f x ^ 2 :=
begin
  rw [← finset.mul_sum, mul_comm],
  have := ennreal.pow_sum_div_card_le_sum_pow s f hf 1,
  simp only [pow_one, one_add_one_eq_two] at this,
  refine (ennreal.div_le_iff_le_mul _ _).1 this,
  { refine or.inr (ne_top_of_lt (ennreal.sum_lt_top (λ x hx, ennreal.pow_ne_top (hf x hx)))) },
  { refine or.inl (ennreal.nat_ne_top _) }
end

end jensen