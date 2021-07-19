import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials
import analysis.special_functions.exp_log
import to_mathlib

/-!
# Polynomial Growth

This file defines polynomial growth of functions via `poly_growth_in_parameter`.
This definition is given in terms of a parameter function `k : α → R`,
 which can specialize to e.g. `id` or `log` to represent polynomial and polylogarithmic growth resp.

The main defintion is given in terms of powers, see `poly_growth_in_parameter_iff` for an equivalent
 formulation in terms of `polynomial`.
-/

section poly_growth_in_parameter

open polynomial asymptotics

/-- A function `f` has polynomial growth in the parameter `k` if `f(x) = O(k(x)^n)` for some `n : ℕ`
  This is equivalent to `f(x) = O(p ∘ k)` for some polynomial `p`, see `poly_growth_in_parameter_iff` -/
def poly_growth_in_parameter {α R S : Type*} [preorder α] [normed_ring R] [normed_ring S]
  (k : α → R) (f : α → S) :=
∃ (n : ℕ), is_O f (λ x, (k x) ^ n) filter.at_top

variables {α : Type*} [preorder α]
variables {R S : Type*} [normed_ring R] [normed_ring S]
variables {𝕜 : Type*} [normed_field 𝕜]

lemma poly_growth_in_parameter_def (k : α → R) (f : α → S) :
  poly_growth_in_parameter k f ↔ ∃ (n : ℕ), is_O f (λ x, (k x) ^ n) filter.at_top :=
iff.rfl

lemma poly_growth_in_parameter.ext {k : α → R} {f g : α → S}
  (hf : poly_growth_in_parameter k f) (hfg : ∀ x, g x = f x) :
  poly_growth_in_parameter k g :=
(funext hfg : g = f).symm ▸ hf

@[simp] lemma poly_growth_in_parameter_parameter (k : α → R) :
  poly_growth_in_parameter k k :=
⟨1, by simpa using is_O_refl k filter.at_top⟩

variable [norm_one_class R]

@[simp] 
lemma poly_growth_in_parameter_const (k : α → R) (s : S) :
  poly_growth_in_parameter k (λ _, s) :=
⟨0, is_O_of_le' filter.at_top (λ x, by simp : ∀ x, ∥s∥ ≤ ∥s∥ * ∥k x ^ 0∥)⟩

lemma poly_growth_in_parameter_one (k : α → R) :
  poly_growth_in_parameter k (1 : α → S) :=
poly_growth_in_parameter_const k 1

lemma poly_growth_in_parameter_zero (k : α → R) :
  poly_growth_in_parameter k (0 : α → S) :=
poly_growth_in_parameter_const k 0

/-- If the parameter is eventually greater than `1`, then polynomial growth in `k` is additive -/
lemma poly_growth_in_parameter_add {k : α → 𝕜}
  {f g : α → R} (hk : ∀ᶠ x in filter.at_top, 1 ≤ ∥k x∥)
  (hf : poly_growth_in_parameter k f) (hg : poly_growth_in_parameter k g) :
  poly_growth_in_parameter k (f + g) :=
let ⟨n, hn⟩ := hf in let ⟨m, hm⟩ := hg in
⟨max n m, is_O.add (hn.trans $ is_O_of_pow_le hk (le_max_left n m)) 
    (hm.trans $ is_O_of_pow_le hk (le_max_right n m))⟩

/-- Polynomial growth is multiplicative regardless of the parameter-/
lemma poly_growth_in_parameter_mul {k : α → 𝕜} {f g : α → R}
  (hf : poly_growth_in_parameter k f) (hg : poly_growth_in_parameter k g) :
  poly_growth_in_parameter k (f * g) :=
let ⟨n, hn⟩ := hf in let ⟨m, hm⟩ := hg in
⟨n + m, (is_O.mul hn hm).trans $ is_O_of_le filter.at_top (λ x, (pow_add (k x) n m) ▸ le_rfl)⟩

lemma poly_growth_in_parameter_pow {k : α → 𝕜} {f : α → R}
  (hf : poly_growth_in_parameter k f) (n : ℕ) :
  poly_growth_in_parameter k (λ x, f x ^ n) :=
let ⟨m, hm⟩ := hf in
⟨m * n, (is_O.pow hm n).trans $ is_O_of_le filter.at_top (λ x, (pow_mul (k x) m n) ▸ le_rfl)⟩

lemma poly_growth_in_parameter_polynomial {k : α → 𝕜} (hk : ∀ᶠ x in filter.at_top, 1 ≤ ∥k x∥) 
  {f : α → R} (hf : poly_growth_in_parameter k f)
  (p : polynomial R) : poly_growth_in_parameter k (λ x, eval (f x) p) :=
begin
  refine p.induction_on (λ c, _) (λ p q hp hq, _) (λ n c h, _),
  { exact (poly_growth_in_parameter_const k c).ext (λ x, eval_C) },
  { exact (poly_growth_in_parameter_add hk hp hq).ext (λ x, eval_add) },
  { exact (poly_growth_in_parameter_mul h (hf)).ext
      (λ x, by simp only [eval_C, eval_mul_X_pow, pi.mul_apply, pow_add (f x) n 1, mul_assoc, pow_one]) }
end

/-- Equivalence of definition in terms of powers and polynomials,
  assuming `𝕜` is a `normed_linear_ordered_field` with an ordered topology (e.g. `ℝ` or `ℚ`) -/
theorem poly_growth_in_parameter_iff {𝕜 : Type*} [normed_linear_ordered_field 𝕜] [order_topology 𝕜] 
  {k : α → 𝕜} (hk : filter.tendsto k filter.at_top filter.at_top) (f : α → R) :
  poly_growth_in_parameter k f ↔ 
    ∃ (p : polynomial 𝕜), is_O f (λ x, eval (k x) p) filter.at_top :=
begin
  refine ⟨λ h, let ⟨n, hn⟩ := h in ⟨X ^ n, by simpa⟩, _⟩,
  rintro ⟨p, hp⟩,
  refine ⟨p.nat_degree, is_O.trans hp _⟩,
  suffices : is_O ((λ a, eval a p) ∘ k) ((λ a, eval a (X ^ p.nat_degree)) ∘ k) filter.at_top,
  by simpa using this,
  have := polynomial.is_O_of_degree_le p (X ^ p.nat_degree) (by simp),
  refine is_O.comp_tendsto this hk,
end

end poly_growth_in_parameter

section poly_growth

/-- A function `f : ℕ → R` has polynomial growth if it is O(p(n)) for some `p : polynomial R`-/
def poly_growth {R : Type*} [preorder R] [normed_ring R] (f : ℕ → R) :=
poly_growth_in_parameter (λ n, ↑n : ℕ → ℚ) f

variables {R : Type*} [preorder R] [normed_ring R] 

@[simp] lemma poly_growth_const (r : R) : 
  poly_growth (λ _, r) :=
poly_growth_in_parameter_const _ _

@[simp] lemma poly_growth_zero :
  poly_growth (0 : ℕ → R) :=
poly_growth_in_parameter_zero _

@[simp] lemma poly_growth_one :
  poly_growth (1 : ℕ → R) :=
poly_growth_in_parameter_one _

-- TODO: generalize `poly_growth` to any situation allowing *something* like this
lemma h_help : ∀ᶠ (x : ℕ) in filter.at_top, 1 ≤ ∥(x : ℚ)∥ :=
begin
  rw filter.eventually_at_top,
  refine ⟨1, λ x hx, le_abs.2 $ or.inl _⟩,
  simpa only [nat.one_le_cast, rat.cast_coe_nat],
end

variables [norm_one_class R]

lemma poly_growth_add {f g : ℕ → R} (hf : poly_growth f) (hg : poly_growth g) :
  poly_growth (f + g) :=
poly_growth_in_parameter_add h_help hf hg

end poly_growth

section log_poly_growth

def log_poly_growth {R : Type*} [normed_ring R] (f : ℝ → R) :=
poly_growth_in_parameter (real.log) f

lemma log_poly_growth_add {f g : ℝ → ℝ}
  (hf : log_poly_growth f) (hg : log_poly_growth g) :
  log_poly_growth (f + g) :=
poly_growth_in_parameter_add one_eventually_le_log hf hg

end log_poly_growth