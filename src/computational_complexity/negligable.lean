import computational_complexity.polynomial_asymptotics

/-!
# Negligable Growth

This file defines the notion of a negligable function `f : ℕ → ℝ`.
For convenience, the definition is given in terms of `is_O`,
  with various lemmas to translate back to the definition in terms of constants
-/

open asymptotics

section to_mathlib

lemma fpow_is_O_fpow_of_le {a b : ℤ} (h : a ≤ b) :
  (is_O (λ (n : ℕ), (n : ℝ) ^ a) (λ n, (n : ℝ) ^ b) filter.at_top) :=
begin
  refine is_O.of_bound 1 _,
  rw filter.eventually_at_top,
  use 2,
  intros x hx,
  simp,
  refine (fpow_le_iff_le _).2 h,
  rw ← nat.cast_one,
  exact nat.cast_lt.2 hx,
end

lemma inv_is_O_inv_iff {l : filter ℕ} (f g : ℕ → ℝ)
  (hf : ∀ᶠ x in l, ∥f x∥ ≠ 0) (hg : ∀ᶠ x in l, ∥g x∥ ≠ 0) :
  is_O (λ n, (f n)⁻¹) (λ n, (g n)⁻¹) l ↔ is_O g f l :=
begin
  let hfg := filter.eventually.and hf hg,
  have hfg : ∀ᶠ x in l, 0 < ∥f x∥ ∧ 0 < ∥g x∥ := begin
    refine filter.mem_sets_of_superset hfg (λ x hx, by simpa using hx),
  end,
  simp only [is_O_iff],
  refine exists_congr (λ c, ⟨λ hc, _, λ hc, _⟩),
  {

    refine filter.mem_sets_of_superset (hc.and hfg) _,
    intros x hx,
    obtain ⟨hx, hx0⟩ := hx,
    simp_rw [ normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
      mul_one, div_le_iff hx0.1, div_mul_eq_mul_div] at hx,
    refine (one_le_div hx0.2).1 hx,
  },
  {
    refine filter.mem_sets_of_superset (hc.and hfg) _,
    intros x hx,
    simp_rw [set.mem_set_of_eq, normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
      mul_one, div_le_iff hx.2.1, div_mul_eq_mul_div],
    refine (one_le_div hx.2.2).2 hx.1,
  },
end

end to_mathlib

def negligable (f : ℕ → ℝ) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

namespace negligable

lemma negligable.trans {f g : ℕ → ℝ} (hg : negligable g)
  (h : is_O f g filter.at_top) : negligable f :=
λ c, h.trans $ hg c

lemma negligable.add {f g : ℕ → ℝ} (hf : negligable f) (hg : negligable g) :
  negligable (f + g) :=
λ c, (hf c).add $ hg c

lemma negligable_of_is_O_pow_neg {f : ℕ → ℝ} (C : ℤ)
  (hf : ∀ (c : ℤ) (hc : c < C), is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligable f :=
begin
  intro c,
  by_cases hc : c < C,
  { exact hf c hc },
  { rw not_lt at hc,
    refine (hf (C - 1) (by linarith)).trans 
      (fpow_is_O_fpow_of_le (le_trans (by linarith) hc)) }
end

lemma negligable_final_iff_const (f : ℕ → ℝ) (C : ℤ) :
  negligable f ↔ ∀ (c : ℤ) (hc : c < C), ∃ (N : ℕ), ∀ n ≥ N, ∥f n∥ ≤ (n : ℝ) ^ c :=
begin
  refine ⟨λ h c hc, _, λ h, _⟩,
  {
    specialize h (c - 1),
    rw is_O_iff at h,
    obtain ⟨k, hk⟩ := h,
    rw filter.eventually_at_top at hk,
    obtain ⟨N, hN⟩ := hk,
    by_cases hk0 : k ≤ 0,
    { refine ⟨N, λ n hn, _⟩,
      refine le_trans (hN n hn) _,
      refine le_trans (mul_nonpos_iff.2 (or.inr ⟨hk0, abs_nonneg _⟩) : _ ≤ 0) (_ : 0 ≤ _),
      refine fpow_nonneg (nat.cast_nonneg n) (c) },
    replace hk0 : 0 < k := by linarith,
    obtain ⟨M, hM'⟩ := exists_nat_gt k,
    have hM : k ≤ ↑M := le_of_lt hM',
    have hM0 : M ≠ 0 := nat.cast_ne_zero.1 (ne_of_lt (lt_trans hk0 hM')).symm,
    use max N M,
    intros n hn,
    rw ge_iff_le at hn,
    rw max_le_iff at hn,
    specialize hN n (hn.1),
    simp [real.norm_eq_abs] at hN ⊢,
    refine le_trans hN _,
    simp,
    have hn0 : (↑n : ℝ) ≠ 0 := λ h, hM0 begin
      simp at h,
      refine le_antisymm (h ▸ hn.2) zero_le',
    end,
    have hn0' : 0 < (↑n : ℝ) := begin
      refine lt_of_le_of_ne _ hn0.symm,
      refine nat.cast_nonneg n,
    end,
    have : abs ((↑n : ℝ) ^ (c - 1)) = (↑n)⁻¹ * (↑n ^ c),
    {
      refine trans (abs_of_nonneg _) _,
      {
        refine fpow_nonneg (le_of_lt hn0') (c - 1),
      },
      {
        rw [fpow_sub_one hn0, mul_comm],
      }
    },
    rw [this, ← mul_assoc],
    have hnc : 0 < (↑n : ℝ) ^ c := fpow_pos_of_pos hn0' c,
    refine (mul_le_iff_le_one_left hnc).2 _,
    calc k * (↑n)⁻¹ ≤ k * k⁻¹ : begin
      refine mul_le_mul le_rfl _ _ (le_of_lt hk0),
      {
        refine (inv_le_inv hn0' hk0).mpr _,
        refine le_trans hM _,
        simp only [nat.cast_le],
        exact hn.2,
      },
      {
        refine inv_nonneg.2 (nat.cast_nonneg n),
      }
    end
      ... = 1 : mul_inv_cancel begin
        refine (ne_of_lt hk0).symm
      end,
  },
  {
    refine negligable_of_is_O_pow_neg C _,
    intros c hc,
    specialize h c hc,
    obtain ⟨N, hN⟩ := h,
    rw is_O_iff,
    use 1,
    rw filter.eventually_at_top,
    refine ⟨N, λ x hx, _⟩,
    specialize hN x hx,
    refine le_trans (hN) _,
    simp,
  },
end

lemma negligable_iff_polynomial (f : ℕ → ℝ) :
  negligable f ↔ ∀ (p : polynomial ℝ) (hp : p ≠ 0), is_O f (λ n, (p.eval ↑n)⁻¹) filter.at_top :=
begin
  refine ⟨λ h p hp, _, λ h, _⟩,
  {
    specialize h (- p.nat_degree),
    refine h.trans _,
    simp only [fpow_neg],
    have h1 : ∀ᶠ (n : ℕ) in filter.at_top, ∥(n : ℝ) ^ (p.nat_degree : ℤ)∥ ≠ 0,
    { rw filter.eventually_at_top,
      refine ⟨1, λ x hx, _⟩,
      rw [ne.def, real.norm_eq_abs, abs_eq_zero],
      refine fpow_ne_zero (p.nat_degree : ℤ) _,
      refine nat.cast_ne_zero.2 _,
      refine ne_of_gt (lt_of_lt_of_le zero_lt_one hx),
    },
    have h2 : ∀ᶠ (n : ℕ) in filter.at_top, ∥p.eval ↑n∥ ≠ 0,
    {
      have := polynomial.eventually_no_roots p hp,
      rw filter.eventually_at_top at this ⊢,
      obtain ⟨x, hx⟩ := this,
      obtain ⟨n, hn⟩ := exists_nat_ge x,
      refine ⟨n, λ m hm, _⟩,
      specialize hx (m : ℝ) (hn.trans (nat.cast_le.2 hm)),
      rw [real.norm_eq_abs, ne.def, abs_eq_zero],
      exact hx,
    },
    refine (inv_is_O_inv_iff _ _ h1 h2).2 _,
    have := polynomial.is_O_of_degree_le p (polynomial.X ^ p.nat_degree) (by simp),
    have := is_O.comp_tendsto this (begin
      rw filter.tendsto_at_top,
      intro x,
      obtain ⟨m, hm⟩ := exists_nat_ge x,
      rw filter.eventually_at_top,
      refine ⟨m, λ y hy, hm.trans _⟩,
      refine nat.cast_le.2 hy,
    end : filter.tendsto (λ (n : ℕ), (↑n : ℝ)) filter.at_top filter.at_top),
    refine this.trans _,
    simp,
    exact is_O_refl _ _,
  },
  {
    refine negligable_of_is_O_pow_neg 0 (λ c hc, _),    
    refine (h (polynomial.X ^ (c.nat_abs)) begin
      refine pow_ne_zero _ _,
      refine polynomial.X_ne_zero,
    end).trans _,
    convert is_O_refl _ _,
    ext x,
    have : (x : ℝ) ^ c.nat_abs = x ^ (-c),
    by simp only [← int.of_nat_nat_abs_of_nonpos (le_of_lt hc), fpow_coe_nat],
    simp [this],
  }
end 

end negligable