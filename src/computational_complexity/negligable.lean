import computational_complexity.polynomial_asymptotics

/-!
# Negligable Growth

This file defines the notion of a negligable function `f : ℕ → ℝ`.
For convenience, the definition is given in terms of `is_O`,
  with various lemmas to translate back to the definition in terms of constants
-/

-- TODO: remove namespace and space them explicitly (e.g. negligable.add)

open asymptotics

def negligable (f : ℕ → ℝ) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

namespace negligable

lemma negligable_of_is_O {f g : ℕ → ℝ} (hg : negligable g)
  (h : is_O f g filter.at_top) : negligable f :=
λ c, h.trans $ hg c

lemma add_negligable {f g : ℕ → ℝ} (hf : negligable f) (hg : negligable g) :
  negligable (f + g) :=
λ c, (hf c).add $ hg c

@[simp] lemma zero_negligable : negligable (λ n, 0) :=
λ c, is_O_zero _ _

lemma negligable_of_eventually_le {f g : ℕ → ℝ} (hg : negligable g)
  (h : ∀ᶠ n in filter.at_top, ∥f n∥ ≤ ∥g n∥) : negligable f :=
hg.negligable_of_is_O $ is_O_iff.2 ⟨1, by simpa using h⟩

lemma negligable_of_is_O_pow_neg {f : ℕ → ℝ} (C : ℤ)
  (hf : ∀ (c : ℤ) (hc : c < C), is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligable f :=
begin
  intro c,
  by_cases hc : c < C,
  { exact hf c hc },
  { exact (hf (C - 1) (by linarith)).trans 
      (fpow_is_O_fpow_of_le (le_trans (by linarith) (not_lt.1 hc))) }
end

-- Equivalence with more traditional definition in terms of constants and monomials
-- Note that it suffices to show `f n ≤ n ^ c` for only sufficiently small `c` values
lemma negligable_final_iff_const (f : ℕ → ℝ) (C : ℤ) :
  negligable f ↔ ∀ (c : ℤ) (hc : c < C), ∃ (N : ℕ), ∀ n ≥ N, ∥f n∥ ≤ (n : ℝ) ^ c :=
begin
  refine ⟨λ h c hc, _, λ h, _⟩,
  { obtain ⟨k, hk⟩ := is_O_iff.1 (h (c - 1)),
    obtain ⟨N, hN⟩ := filter.eventually_at_top.1 hk,
    by_cases hk0 : k ≤ 0,
    { refine ⟨N, λ n hn, (hN n hn).trans ((mul_nonpos_iff.2 (or.inr ⟨hk0, abs_nonneg _⟩)).trans _)⟩,
      refine fpow_nonneg (nat.cast_nonneg n) c, },
    replace hk0 : 0 < k := by linarith,
    obtain ⟨M, hM'⟩ := exists_nat_gt k,
    have hM : k ≤ ↑M := le_of_lt hM',
    have hM0 : M ≠ 0 := nat.cast_ne_zero.1 (ne_of_lt (lt_trans hk0 hM')).symm,
    refine ⟨max N M, λ n hn, _⟩,
    rw [ge_iff_le, max_le_iff] at hn,
    refine le_trans (hN n hn.1) _,
    have hn0 : (↑n : ℝ) ≠ 0 := λ h, hM0 (le_antisymm ((nat.cast_eq_zero.1 h) ▸ hn.2) zero_le'),
    have hn0' : 0 < (↑n : ℝ) := lt_of_le_of_ne (nat.cast_nonneg n) hn0.symm,
    have : ∥(↑n : ℝ) ^ (c - 1)∥ = (↑n)⁻¹ * (↑n ^ c) :=
      trans (abs_of_nonneg (fpow_nonneg (le_of_lt hn0') (c - 1))) (by field_simp [fpow_sub_one hn0]),
    rw [this, ← mul_assoc],
    refine (mul_le_iff_le_one_left (fpow_pos_of_pos hn0' c)).2 _,
    calc k * (↑n)⁻¹ ≤ k * k⁻¹ : mul_le_mul le_rfl ((inv_le_inv hn0' hk0).2 (le_trans hM (nat.cast_le.2 hn.2)))
        (inv_nonneg.2 (nat.cast_nonneg n)) (le_of_lt hk0)
      ... = 1 : mul_inv_cancel (ne_of_lt hk0).symm },
  { refine negligable_of_is_O_pow_neg C (λ c hc, _),
    obtain ⟨N, hN⟩ := h c hc,
    refine is_O_iff.2 ⟨1, filter.eventually_at_top.2 ⟨N, λ x hx, (hN x hx).trans (by simp)⟩⟩ },
end

-- Equivalence between definitions in terms of integer powers and general polynomials
lemma negligable_iff_polynomial (f : ℕ → ℝ) :
  negligable f ↔ ∀ (p : polynomial ℝ) (hp : p ≠ 0), is_O f (λ n, (p.eval ↑n)⁻¹) filter.at_top :=
begin
  refine ⟨λ h p hp, _, λ h, _⟩,
  { refine (h (-p.nat_degree)).trans _,
    have h2 : ∀ᶠ (n : ℕ) in filter.at_top, ∥p.eval ↑n∥ ≠ 0,
    { have : ∀ᶠ (n : ℕ) in filter.at_top, p.eval ↑n ≠ 0,
      from comap_thing.symm ▸ filter.eventually_comap' (polynomial.eventually_no_roots p hp),
      refine filter.mem_sets_of_superset this (λ x hx h, hx (norm_eq_zero.1 h)) },
    simp only [fpow_neg],
    refine (inv_is_O_inv_iff _ _ (eventually_fpow_ne_zero p.nat_degree) h2).2 _,
    have := polynomial.is_O_of_degree_le p (polynomial.X ^ p.nat_degree) (by simp),
    refine (is_O.comp_tendsto this nat_coe_tendsto).trans _,
    simp only [polynomial.eval_X, polynomial.eval_pow, gpow_coe_nat],
    exact is_O_refl _ _ },
  { refine negligable_of_is_O_pow_neg 0 (λ c hc, _),    
    refine (h (polynomial.X ^ c.nat_abs) $ pow_ne_zero _ polynomial.X_ne_zero).trans _,
    have : ∀ (x : ℕ), (x : ℝ) ^ c.nat_abs = x ^ (-c),
    from λ x, by simp only [←int.of_nat_nat_abs_of_nonpos (le_of_lt hc), gpow_coe_nat],
    simp only [this, polynomial.eval_X, inv_inv', polynomial.eval_pow, fpow_neg],
    exact is_O_refl _ filter.at_top }
end

@[simp]
lemma const_mul_negligable_iff (f : ℕ → ℝ) {c : ℝ} (hc : c ≠ 0) :
  negligable (λ n, c * f n) ↔ negligable f :=
forall_congr (λ x, ⟨λ h, is_O.trans (is_O_self_const_mul c hc f filter.at_top) h, 
  λ h, is_O.trans (is_O_const_mul_self c f filter.at_top) h⟩)

@[simp]
lemma x_mul_negligable_iff (f : ℕ → ℝ) :
  negligable (λ n, (n : ℝ) * f n) ↔ negligable f :=
begin
  refine ⟨λ h, _, λ h c, _⟩,
  { refine h.negligable_of_eventually_le (filter.eventually_at_top.2 ⟨1, λ x hx, _⟩),
    simp only [normed_field.norm_mul, real.norm_coe_nat],
    by_cases hfx : f x = 0,
    { simp [hfx] },
    { exact (le_mul_iff_one_le_left (norm_pos_iff.2 hfx)).2 (nat.one_le_cast.2 hx) } },
  { refine (is_O.mul (is_O_refl (λ (n : ℕ), (n : ℝ)) filter.at_top) (h (c - 1))).trans (is_O_of_le _ (λ x, _)),
    simp only [normed_field.norm_mul, real.norm_coe_nat, normed_field.norm_fpow],
    by_cases hx : (x : ℝ) = 0,
    { by_cases hc : c = 0,
      { simp [hx, hc, zero_le_one] },
      { simp [hx, zero_fpow c hc] } },
    { rw [mul_comm (x : ℝ), fpow_sub_one hx, mul_assoc, inv_mul_cancel hx, mul_one] } }
end

@[simp]
lemma pow_mul_negligable_iff (f : ℕ → ℝ) (c : ℕ) :
  negligable (λ n, (n : ℝ) ^ c * f n) ↔ negligable f :=
begin
  induction c with c hc,
  { simp only [one_mul, pow_zero] },
  { simp_rw [← hc, pow_succ, mul_assoc, x_mul_negligable_iff] }
end

theorem mul_polynomial_negligable_iff (f : ℕ → ℝ) (p : polynomial ℝ) (hp0 : p ≠ 0) :
  negligable (λ n, (p.eval n) * f n) ↔ negligable f :=
begin
  refine ⟨λ h, _, _⟩,
  { by_cases hp : 1 ≤ p.degree,
    { have : ∀ᶠ (n : ℕ) in filter.at_top, 1 ≤ ∥polynomial.eval ↑n p∥ :=
        comap_thing.symm ▸ filter.eventually_comap' (poly_help hp 1),
      refine (negligable_of_eventually_le h $ filter.mem_sets_of_superset this (λ x hx, _)),
      simp only [normed_field.norm_mul, set.mem_set_of_eq] at ⊢ hx,
      by_cases hfx : f x = 0,
      { simp only [hfx, norm_zero, mul_zero]},
      { refine (le_mul_iff_one_le_left (norm_pos_iff.2 hfx)).2 hx } },
    { replace hp : p.degree ≤ 0,
      { rw not_le at hp,
        contrapose! hp,
        rwa nat.with_bot.one_le_iff_zero_lt },
      have hp_C := polynomial.eq_C_of_degree_le_zero hp,
      have hpc0 : p.coeff 0 ≠ 0 := λ h, hp0 (hp_C.trans (by simp only [h, ring_hom.map_zero])),
      rw [hp_C] at h,
      simpa only [polynomial.eval_C, const_mul_negligable_iff _ hpc0] using h } },
  { refine λ h, polynomial.induction_on' p (λ p q hp hq, _) (λ n x, _),
    { simpa [polynomial.eval_add, add_mul] using add_negligable hp hq },
    { by_cases hx : x = 0,
      { simp only [hx, zero_negligable, zero_mul, polynomial.monomial_zero_right, polynomial.eval_zero] },
      { simpa only [mul_assoc x, const_mul_negligable_iff _ hx, 
          pow_mul_negligable_iff, polynomial.eval_monomial] } } }
end

-- TODO: implement something general like this
-- theorem two_pow_negligable : negligable (λ n, 1 / 2 ^ n) :=
-- begin
--   refine (negligable_final_iff_const _ 0).2 _,
--   intros c hc,
--   simp,
--   sorry,
-- end

end negligable