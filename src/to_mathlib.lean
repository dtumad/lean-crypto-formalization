import data.bitvec.basic
import measure_theory.probability_mass_function
import analysis.special_functions.exp_log
import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials 

-- Collection of random statements that maybe should eventually move to mathlib

lemma ite_le {A : Type*} [has_le A] {a b c : A} (p : Prop) [decidable p]
  (hab : b ≤ a) (hac : c ≤ a) : ite p b c ≤ a :=
by split_ifs; assumption

section asymptotics

open asymptotics

lemma is_O_of_pow_le {α 𝕜 : Type*} [normed_field 𝕜] {l : filter α}
  {f : α → 𝕜} (hf : ∀ᶠ x in l, ∥f x∥ ≥ 1) {n m : ℕ} (hnm : n ≤ m) :
  is_O (λ x, (f x) ^ n) (λ x, (f x) ^ m) l :=
begin
  rw is_O_iff,
  refine ⟨1, filter.eventually_of_mem hf (λ x hx, _)⟩,
  simp only [one_mul, normed_field.norm_pow],
  refine pow_le_pow hx hnm,
end 

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

end asymptotics

def decidable_eq_of_prod_left {A B : Type*} [inhabited B] [h : decidable_eq (A × B)] : 
  decidable_eq A :=
λ a a', decidable.rec (λ h, is_false (λ h', h (prod.mk.inj_iff.mpr ⟨h', rfl⟩))) 
  (λ h, is_true (prod.mk.inj_iff.mp h).1) (h ⟨a, arbitrary B⟩ ⟨a', arbitrary B⟩)

@[simp] lemma card_bitvec {n : ℕ} : fintype.card (bitvec n) = 2 ^ n :=
by rw [card_vector n, fintype.card_bool]

section const_pmf

lemma sum_inv_fintype_card_eq_one {A : Type*} [fintype A] [inhabited A] :
  has_sum (λ (a : A), (fintype.card A : nnreal)⁻¹) 1 :=
begin
  convert has_sum_fintype (λ (a : A), (fintype.card A : nnreal)⁻¹),
  rw [finset.sum_const, nsmul_eq_mul],
  refine (div_self _).symm,
  exact nat.cast_ne_zero.2 (finset.card_ne_zero_of_mem (by simp : arbitrary A ∈ _)),
end

/-- Definition of a uniform `pmf` on a finite type -/
noncomputable def pmf.const (α : Type*) [fintype α] [inhabited α] : pmf α :=
⟨λ a, (fintype.card α : nnreal)⁻¹, sum_inv_fintype_card_eq_one⟩

@[simp] lemma pmf.const_apply {α : Type*} [fintype α] [inhabited α]
  (a : α) : pmf.const α a = (fintype.card α : nnreal)⁻¹ := rfl

lemma card_ne_zero_of_inhabited {α : Type*} [fintype α] [inhabited α] : 
  fintype.card α ≠ 0 :=
finset.card_ne_zero_of_mem (finset.mem_univ (arbitrary α))

end const_pmf

section log_exp

open real

lemma log_le_of_nonneg {x : ℝ} (hx : x ≥ 0) : log x ≤ x :=
begin
  cases lt_or_eq_of_le hx with hx' hx',
  { calc log x ≤ log (exp x) : (log_le_log hx' (exp_pos x)).mpr 
        (trans (by linarith) (add_one_le_exp_of_nonneg hx))
      ... = x : by simp },
  { simp [← hx'] }
end

lemma neg_log_le_of_nonneg {x : ℝ} (hx : x ≥ 1) : - log x ≤ x :=
calc - log x ≤ 0 : neg_nonpos.mpr $ log_nonneg hx
        ... ≤ 1 : zero_le_one
        ... ≤ x : hx

lemma one_eventually_le_log : ∀ᶠ (x : ℝ) in filter.at_top, 1 ≤ ∥real.log x∥ :=
begin
  simp only [filter.eventually_at_top, ge_iff_le],
  refine ⟨real.exp 1, λ x hx, _⟩,
  suffices : 1 ≤ real.log x,
  from real.norm_eq_abs (real.log x) ▸ le_abs.2 (or.inl this),
  rwa [← real.log_exp 1, real.log_le_log (real.exp_pos 1) (lt_of_lt_of_le (real.exp_pos 1) hx)],
end

lemma log_ge_of_ge_exp {x y : ℝ} (h : x ≥ real.exp y) : real.log x ≥ y :=
calc y = real.log (real.exp y) : (real.log_exp y).symm
      ... ≤ real.log x : (real.log_le_log (real.exp_pos y) (lt_of_lt_of_le (real.exp_pos y) h)).mpr h


end log_exp

lemma poly_help {p : polynomial ℝ} (hp : 1 ≤ p.degree) (c : ℝ) :
  ∀ᶠ x in filter.at_top, c ≤ ∥p.eval x∥ :=
begin
  have := polynomial.abs_tendsto_at_top p hp,
  rw filter.tendsto_at_top at this,
  specialize this c,
  exact this,
end

lemma eq_zero_of_norm_fpow_eq_zero (r : ℝ) (z : ℤ) (h : ∥r ^ z∥ = 0) : r = 0 :=
by simpa [real.norm_eq_abs] using fpow_eq_zero (normed_field.norm_fpow r z ▸ h : ∥r∥^z = 0)

lemma eventually_fpow_ne_zero (z : ℤ) : ∀ᶠ (n : ℕ) in filter.at_top, ∥(n : ℝ) ^ z∥ ≠ 0 :=
begin
  have : ∀ᶠ (n : ℕ) in filter.at_top, (n : ℝ) ≠ 0,
  { simp only [filter.eventually_at_top, ge_iff_le, ne.def, nat.cast_eq_zero],
    refine ⟨1, λ b hb, by linarith⟩ },
  exact filter.mem_sets_of_superset this (λ x hx, mt (eq_zero_of_norm_fpow_eq_zero _ _) hx),
end

lemma nat_coe_tendsto {𝕜 : Type*} [normed_linear_ordered_field 𝕜] [archimedean 𝕜] : 
  filter.tendsto (λ (n : ℕ), (↑n : 𝕜)) filter.at_top filter.at_top :=
begin
  refine filter.tendsto_at_top.2 (λ x, _),
  obtain ⟨m, hm⟩ := exists_nat_ge x,
  rw filter.eventually_at_top,
  refine ⟨m, λ y hy, hm.trans $ nat.cast_le.2 hy⟩,
end

lemma comap_thing : (filter.at_top : filter ℕ) = filter.comap (λ n, ↑n : ℕ → ℝ) filter.at_top :=
begin
  ext t,
  split,
  {
    intro h,
    rw filter.mem_comap_sets,
    rw filter.mem_at_top_sets at h,
    obtain ⟨a, ha⟩ := h,
    refine ⟨set.Ici ↑a, _, _⟩,
    {
      simp,
      refine ⟨↑a, λ b, id⟩,
    },
    {
      intros x hx,
      rw [set.mem_preimage, set.mem_Ici, nat.cast_le] at hx,
      refine ha x hx,
    }
  },
  {
    intro h,
    rw filter.mem_comap_sets at h,
    obtain ⟨s, hs, h⟩ := h,
    rw filter.mem_at_top_sets at hs ⊢,
    obtain ⟨a, ha⟩ := hs,
    obtain ⟨b, hb⟩ := exists_nat_ge a,
    refine ⟨b, λ x hx, h _⟩,
    rw set.mem_preimage,
    refine ha x (hb.trans _),
    rw nat.cast_le,
    exact hx,
  }
end