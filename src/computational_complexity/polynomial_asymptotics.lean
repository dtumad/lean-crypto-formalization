import analysis.asymptotics.asymptotics
import data.polynomial
import data.real.nnreal
import analysis.special_functions.polynomials
import analysis.special_functions.exp_log

universes u v

open_locale nnreal

open asymptotics

section to_mathlib
-- General facts that should probably be ported to mathlib eventually

lemma is_O_at_top_iff {α β γ : Type*} [nonempty α]
  [semilattice_sup α] [semilattice_sup β] [semilattice_sup γ]
  [has_norm β] [has_norm γ] (f : α → β) (g : α → γ) :
  is_O f g filter.at_top ↔ ∃ M x₀, ∀ x, x₀ ≤ x → ∥f x∥ ≤ M * ∥g x∥ :=
by simp only [is_O_iff, filter.eventually_at_top]

lemma is_O_of_pow_le {α 𝕜 : Type*} [normed_linear_ordered_field 𝕜] {l : filter α}
  {f : α → 𝕜} (hf : ∀ᶠ x in l, ∥f x∥ ≥ 1) {n m : ℕ} (hnm : n ≤ m) :
  is_O (λ x, (f x) ^ n) (λ x, (f x) ^ m) l :=
begin
  rw is_O_iff,
  refine ⟨1, filter.eventually_of_mem hf (λ x hx, _)⟩,
  simp only [one_mul, normed_field.norm_pow],
  refine pow_le_pow hx hnm,
end 

end to_mathlib

section poly_growth
open polynomial

/-- TODO: Define this better -/
def negligable {α R : Type u} [normed_ring R] [preorder α] (f : α → R) :=
filter.tendsto f filter.at_top (nhds 0)

/-- Predicate for functions that have polynomial growth -/
def poly_growth {R : Type u} [normed_ring R] [preorder R] (f : R → R) :=
∃ (p : polynomial R), is_O f (λ a, eval a p) filter.at_top

variables {R : Type u} [normed_ring R] [preorder R]

@[simp] lemma poly_growth_const (b : R) : poly_growth (λ _, b) :=
⟨C b, is_O_of_le filter.at_top (λ x, by simp)⟩

@[simp] lemma poly_growth_one : poly_growth (1 : R → R) :=
poly_growth_const 1

@[simp] lemma poly_growth_zero : poly_growth (0 : R → R) :=
poly_growth_const 0

@[simp] lemma poly_growth_id : poly_growth (id : R → R) :=
⟨X, is_O_of_le filter.at_top (λ x, by simp)⟩

variables {𝕜 : Type u} [normed_linear_ordered_field 𝕜] [order_topology 𝕜]

lemma poly_growth_mul {f g : 𝕜 → 𝕜} (hf : poly_growth f)
  (hg : poly_growth g) : poly_growth (f * g) :=
let ⟨p, hp⟩ := hf, ⟨q, hq⟩ := hg in 
  ⟨p * q, by simpa using is_O.mul hp hq⟩

lemma poly_growth_pow {f : 𝕜 → 𝕜} (hf : poly_growth f) (n : ℕ) :
  poly_growth (f ^ n) :=
nat.rec_on n ((pow_zero f).symm ▸ poly_growth_one)
  (λ n hn, (pow_succ f n).symm ▸ poly_growth_mul hf hn)

lemma poly_growth_iff_is_O_monomial (f : 𝕜 → 𝕜) :
  poly_growth f ↔ ∃ (n : ℕ), is_O f (λ b, b ^ n) filter.at_top :=
⟨λ h, let ⟨p, hp⟩ := h in ⟨p.nat_degree, is_O.trans hp (is_O.trans
  (is_O_of_degree_le p (X ^ p.nat_degree) (by simp)) (by simp [is_O_refl]))⟩, 
λ h, let ⟨n, hn⟩ := h in ⟨X ^ n, is_O.trans hn (is_O_of_le filter.at_top (λ x, by simp))⟩⟩

lemma poly_growth_add {f g : 𝕜 → 𝕜} (hf : poly_growth f)
  (hg : poly_growth g) : poly_growth (f + g) :=
let ⟨p, hp⟩ := hf, ⟨q, hq⟩ := hg in
begin
  by_cases hpq : p = 0 ∨ q = 0,
  { cases hpq with hp0 hq0,
    { simp only [hp0, eval_zero] at hp,
      refine ⟨q, is_O.add (is_O.trans hp (is_O_zero _ _)) hq⟩ },
    { simp only [hq0, eval_zero] at hq,
      refine ⟨p, is_O.add hp (is_O.trans hq (is_O_zero _ _))⟩ } },
  { rw not_or_distrib at hpq,
    refine ⟨p * q, is_O.add (is_O.trans hp (is_O_of_degree_le p (p * q) (degree_le_mul_left _ hpq.2)))
      (is_O.trans hq (is_O_of_degree_le q (p * q) (mul_comm q p ▸ (degree_le_mul_left _ hpq.1))))⟩ }
end

end poly_growth

section log_poly_growth
open polynomial
open real

def log_poly_growth (f : ℝ → ℝ) := 
∃ (k : ℕ), is_O f (λ a, (log a) ^ k) filter.at_top

lemma log_poly_growth_iff (f : ℝ → ℝ) :
  log_poly_growth f ↔ ∃ (k : ℕ), is_O f (λ a, (log a) ^ k) filter.at_top :=
iff.rfl

lemma log_poly_growth_iff_is_O_log_pow (f : ℝ → ℝ) :
  log_poly_growth f ↔ ∃ (p : polynomial ℝ), is_O f (λ a, eval (log a) p) filter.at_top :=
begin
  refine ⟨λ h, let ⟨k, hk⟩ := h in ⟨X ^ k, by simpa only [eval_X, eval_pow]⟩, _⟩,
  rintro ⟨p, hp⟩,
  refine ⟨p.nat_degree, is_O.trans hp _⟩,
  suffices : is_O ((λ a, eval a p) ∘ log) ((λ a, eval a (X ^ p.nat_degree)) ∘ log) filter.at_top,
  by simpa using this,
  exact is_O.comp_tendsto (polynomial.is_O_of_degree_le _ _ (by simp)) tendsto_log_at_top,
end

@[simp] lemma log_poly_growth_const (b : ℝ) : log_poly_growth (λ _, b) :=
⟨0, by simpa using is_O_const_const b (zero_ne_one.symm : (1 : ℝ) ≠ 0) filter.at_top⟩

@[simp] lemma log_poly_growth_one : log_poly_growth 1 :=
log_poly_growth_const 1

@[simp] lemma log_poly_growth_zero : log_poly_growth 0 :=
log_poly_growth_const 0

@[simp] lemma log_poly_growth_log : log_poly_growth real.log :=
⟨1, by simp [is_O_refl]⟩

lemma log_poly_growth_mul {f g : ℝ → ℝ} (hf : log_poly_growth f)
  (hg : log_poly_growth g) : log_poly_growth (f * g) :=
let ⟨a, ha⟩ := hf, ⟨b, hb⟩ := hg in 
  ⟨a + b, by simpa [pow_add] using is_O.mul ha hb⟩

lemma log_poly_growth_pow {f : ℝ → ℝ} (hf : log_poly_growth f) (n : ℕ) :
  log_poly_growth (f ^ n) :=
nat.rec_on n ((pow_zero f) ▸ log_poly_growth_one)
  (λ n hn, (pow_succ f n) ▸ log_poly_growth_mul hf hn)

lemma log_ge_of_ge_exp {x y : ℝ} (h : x ≥ exp y) : log x ≥ y :=
calc y = log (exp y) : (log_exp y).symm
      ... ≤ log x : (log_le_log (exp_pos y) (lt_of_lt_of_le (exp_pos y) h)).mpr h

theorem log_poly_growth_add {f g : ℝ → ℝ} (hf : log_poly_growth f)
  (hg : log_poly_growth g) : log_poly_growth (f + g) :=
let ⟨a, ha⟩ := hf, ⟨b, hb⟩ := hg in 
have hx : ∀ᶠ (x : ℝ) in filter.at_top, ∥log x∥ ≥ 1 := 
  filter.eventually_at_top.mpr ⟨exp 1, λ x hx, le_abs.mpr (or.inl (log_ge_of_ge_exp hx))⟩,
⟨max a b, is_O.add (is_O.trans ha (is_O_of_pow_le hx (le_max_left a b)))
  (is_O.trans hb (is_O_of_pow_le hx (le_max_right a b)))⟩

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

theorem poly_growth_of_log_poly_growth {f : ℝ → ℝ} (hf : log_poly_growth f) :
  poly_growth f :=
begin
  obtain ⟨k, hk⟩ := hf,
  refine ⟨X ^ k, is_O.trans hk _⟩,
  simp only [eval_X, eval_pow],
  rw is_O_iff,
  refine ⟨1, _⟩,
  rw filter.eventually_at_top,
  refine ⟨1, λ x hx, _⟩,
  simp [real.norm_eq_abs],
  by_cases hk : k = 0,
  { simp [hk] },
  { refine pow_le_pow_of_le_left (abs_nonneg (log x)) (abs_le_abs _ _) k,
    { refine log_le_of_nonneg (by linarith) },
    { refine neg_log_le_of_nonneg (by linarith) } } 
end

end log_poly_growth