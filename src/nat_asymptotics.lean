import analysis.asymptotics.asymptotics
import data.polynomial
import data.real.nnreal

universes u v

open_locale nnreal

section nat_asymptotics
open asymptotics

section nonneg_norm

class has_nonneg_norm (α : Type u) extends has_norm α :=
(nonneg_norm : ∀ (a : α), ∥a∥ ≥ 0)

@[simp] lemma norm_ge_zero {α : Type u} [h : has_nonneg_norm α] (a : α) : ∥a∥ ≥ 0 :=
has_nonneg_norm.nonneg_norm a

instance nat.norm : has_nonneg_norm ℕ :=
{ norm := λ n, ↑n,
  nonneg_norm := nat.cast_nonneg }

@[simp] lemma norm_nat_def {n : ℕ} : ∥n∥ = ↑n := rfl

@[simp] lemma norm_nat_le_iff {n m : ℕ} : 
  ∥n∥ ≤ ∥m∥ ↔ n ≤ m := by simp

instance nnreal.norm : has_nonneg_norm ℝ≥0 :=
{ norm := λ n, ↑n,
  nonneg_norm := λ n, n.2 }

@[simp] lemma norm_nnreal_def {r : ℝ≥0} : ∥r∥ = ↑r := rfl

@[simp] lemma norm_nnreal_le_iff {r p : ℝ≥0} :
  ∥r∥ ≤ ∥p∥ ↔ r ≤ p := by simp

end nonneg_norm

section is_O_at_top

variables {α β γ ν : Type*} [nonempty ν]
variables [semilattice_sup α] [semilattice_sup β] [semilattice_sup γ] [semilattice_sup ν]

lemma is_O_at_top_iff [has_norm β] [has_norm α] (f : ν → α) (g : ν → β) :
  is_O f g filter.at_top ↔ ∃ M x₀, ∀ x, x₀ ≤ x → ∥f x∥ ≤ M * ∥g x∥ :=
by simp only [is_O_iff, filter.eventually_at_top]

theorem is_O_at_top_trans {ν : Type*} [nonempty ν] [linear_order ν]
  [has_nonneg_norm α] [has_nonneg_norm β] [has_nonneg_norm γ]
  {f : ν → α} {g : ν → β} {h : ν → γ}
  (hfg : is_O f g filter.at_top) (hgh : is_O g h filter.at_top) :
  is_O f h filter.at_top :=
begin
  rw is_O_at_top_iff at hfg hgh ⊢,
  obtain ⟨M, x₀, hM⟩ := hfg,
  obtain ⟨M', x₀', hM'⟩ := hgh,
  have := lt_trichotomy 0 M,
  cases lt_trichotomy 0 M with hM0 hM0,
  { refine ⟨M * M', max x₀ x₀', λ x hx, _⟩,
    rw max_le_iff at hx,
    rw mul_assoc,
    refine trans (hM x hx.1) _,
    rw mul_le_mul_left hM0,
    exact (hM' x hx.2) },
  { cases hM0 with hM0 hM0,
    { refine ⟨M, x₀, λ x hx, _⟩,
      refine trans (hM x hx) (by simp [hM0.symm]) },
    { refine ⟨-M * M', max x₀ x₀', λ x hx, _⟩,
      rw [max_le_iff] at hx,
      have : ∥f x∥ ≤ -M * ∥g x∥,
      { refine trans (hM x hx.1) _,
        cases eq_or_lt_of_le (norm_ge_zero (g x)) with hgx hgx,
        { simp only [←hgx, mul_zero] },
        { simp only [mul_le_mul_right hgx, le_neg_self_iff, le_of_lt hM0] } },
      refine trans this _,
      rw [mul_assoc, mul_le_mul_left (by linarith only [hM0] : 0 < -M)],
      exact hM' x hx.2 } }
end

end is_O_at_top

-- lemma polynomial_is_O_pow_degree'' {α β : Type u} [normed_ring α]
--   [H : ordered_add_comm_monoid α]
--   [semilattice_sup β] [semiring β] [nonempty β] [has_lift_t β α]
--   -- [ordered_add_comm_monoid α]
--   (p : polynomial α) (h : ∀ (a b : α), a ≤ b → ∥a∥ ≤ ∥b∥)
--   :
--   is_O (λ (x : β), polynomial.eval ↑x p) 
--     (λ (x : β), (↑x : α) ^ p.nat_degree) filter.at_top :=
-- begin
--   rw is_O_iff,
--   refine ⟨∥ (finsupp.sum p (λ (e : ℕ), id)) ∥, _⟩,
--   rw filter.eventually_at_top,
--   refine ⟨1, λ b hb, _⟩,
--   refine trans _ (norm_mul_le _ _),
--   refine h _ _ _,
--   simp only [finsupp.sum_mul, polynomial.eval_eq_sum],
--   simp only [finsupp.sum],
  
--   refine @finset.sum_le_sum ℕ α p.support _ _ H _,


--   -- rw is_O_at_top_iff,
--   -- refine ⟨∥ (finsupp.sum p (λ (e : ℕ), id)) ∥, 1, λ b hb, _⟩,
--   -- refine trans _ (norm_mul_le _ _),
--   -- simp [finsupp.sum_mul, polynomial.eval_eq_sum],
--   -- refine h _ _ _,
--   sorry,
-- end

-- @[simp] lemma norm_rat_def {q : ℚ} : ∥q∥ = ∥(q : ℝ)∥ := rfl

-- lemma norm_sum_le {α : Type u} [normed_group α] : ℕ :=
-- begin

-- end

lemma is_O_const_add_iff {f : ℚ → ℚ} {g : ℚ → ℚ} {c : ℚ} : 
  is_O (λ x, f x + c) g filter.at_top ↔ is_O f g filter.at_top :=
begin
  sorry,
end

@[simp] lemma is_O_at_top_mul_left {f : ℚ → ℚ} {g : ℚ → ℚ} :
  is_O (λ x, f x * x) (λ x, g x * x) filter.at_top ↔ is_O f g filter.at_top :=
begin
  sorry,
end

lemma rat_polynomial_is_O_pow_degree (p : polynomial ℚ) :
  is_O (λ x, polynomial.eval x p) (λ x, x ^ p.nat_degree) filter.at_top :=
begin
  refine p.rec_on_horner _ _ _,
  { simp only [polynomial.nat_degree_zero, pow_zero, polynomial.eval_zero],
    refine is_O_of_le _ (λ _, (by simpa using zero_le_one)) },
  {
    intros p c hp hc h,
    simp only [polynomial.eval_C, polynomial.eval_add, is_O_const_add_iff],
    refine h.trans _,
    rw is_O_at_top_iff,
    refine ⟨1, 1, λ x hx, _⟩,
    simp only [one_mul, normed_field.norm_pow],
    refine pow_le_pow _ _,
    { refine le_abs.mpr (or.inl (by rwa [← rat.cast_one, rat.cast_le])) },
    {
      refine polynomial.nat_degree_le_nat_degree (polynomial.degree_le_degree _),
      simp only [polynomial.coeff_add, polynomial.coeff_nat_degree],
      rw polynomial.coeff_C,
      split_ifs with hp' hp',
      { rw [polynomial.nat_degree_eq_zero_iff_degree_le_zero,
          polynomial.degree_le_zero_iff, hp] at hp',
        rwa [hp', polynomial.leading_coeff_C, zero_add] },
      { rw [add_zero, ne.def, polynomial.leading_coeff_eq_zero_iff_deg_eq_bot,
          polynomial.degree_eq_bot],
        refine λ h, hp' (h.symm ▸ polynomial.nat_degree_zero) }
    }, 
  },
  {
    intros p hp h,
    simp only [polynomial.eval_X, polynomial.eval_mul],
    rw polynomial.nat_degree_mul hp polynomial.X_ne_zero,
    rw polynomial.nat_degree_X,
    simp [pow_succ'],
    exact h,
  },
end

lemma polynomial_is_O_pow_degree (p : polynomial ℕ) :
  is_O (λ x, polynomial.eval x p) (λ x, x ^ p.nat_degree) filter.at_top :=
begin
  rw is_O_at_top_iff,
  refine ⟨∥ (finsupp.sum p (λ (e : ℕ), id)) ∥, 1, λ b hb, _⟩,
  simp only [norm_nat_def, ← nat.cast_pow, ← nat.cast_mul, nat.cast_le,
    polynomial.eval_eq_sum, finsupp.sum_mul],
  refine finset.sum_le_sum (λ x hx, mul_le_mul le_rfl (pow_le_pow hb 
    (polynomial.le_nat_degree_of_mem_supp x hx)) zero_le' zero_le'),
end

lemma polynomial_is_O_pow_degree' (p : polynomial ℝ≥0) :
  is_O (λ x, polynomial.eval x p) (λ x, x ^ p.nat_degree) filter.at_top :=
begin
  rw is_O_at_top_iff,
  refine ⟨∥ (finsupp.sum p (λ (e : ℕ), id)) ∥, 1, λ b hb, _⟩,
  simp only [norm_nnreal_def, ← nnreal.coe_mul, ← nnreal.coe_pow, nnreal.coe_le_coe,
    polynomial.eval_eq_sum, finsupp.sum_mul],
  refine finset.sum_le_sum (λ x hx, mul_le_mul le_rfl (pow_le_pow hb 
    (polynomial.le_nat_degree_of_mem_supp x hx)) bot_le bot_le),
end

variables {α β : Type*}

/-- Predicate for functions that have polynomial growth -/
def poly_growth [semiring β] [preorder α] [has_norm α] [has_norm β] 
  [has_lift_t α β] (f : α → β) := 
∃ (p : polynomial β), is_O f (λ (a : α), polynomial.eval ↑a p) filter.at_top

-- theorem poly_growth_iff (f : ℕ → ℕ) :
--   poly_growth f ↔ ∃ (m : ℕ), is_O f (λ n, n ^ m) filter.at_top :=
-- ⟨λ h, let ⟨p, hp⟩ := h in ⟨p.nat_degree, is_O_at_top_trans hp (polynomial_is_O_pow_degree p)⟩,
--   λ h, let ⟨m, hm⟩ := h in ⟨polynomial.X ^ m, by simpa⟩⟩

theorem poly_growth_iff'' (f : ℕ → ℚ) :
  poly_growth f ↔ ∃ (m : ℕ), is_O f (λ n, (n : ℚ) ^ m) filter.at_top :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    obtain ⟨p, hp⟩ := h,
    refine ⟨p.nat_degree, _⟩,
    refine is_O.trans hp _,
  },
  {
    sorry,
  }
end

theorem poly_growth_iff' (f : ℕ → ℝ≥0) :
  poly_growth f ↔ ∃ (m : ℕ), is_O f (λ n, (n : nnreal) ^ m) filter.at_top :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    obtain ⟨p, hp⟩ := h,
    refine ⟨p.nat_degree, is_O_at_top_trans hp _⟩,
    sorry,
  },
  {
    sorry,
  }
end 

end nat_asymptotics