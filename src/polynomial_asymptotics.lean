import analysis.asymptotics.asymptotics
import data.polynomial
import data.real.nnreal
import analysis.special_functions.polynomials

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

lemma norm_le_norm_add_const_of_dist_le {α : Type u} [normed_group α]
  {a b : α} {c : ℝ} (h : dist a b ≤ c) : ∥a∥ ≤ ∥b∥ + c :=
calc ∥a∥ = ∥a - b + b∥ : by rw sub_add_cancel a b
    ... ≤ ∥a - b∥ + ∥b∥ : norm_add_le (a - b) b
    ... = (dist a b) + ∥b∥ : by rw normed_group.dist_eq
    ... ≤ c + ∥b∥ : add_le_add h le_rfl
    ... ≤ ∥b∥ + c : by rw (add_comm c ∥b∥)

theorem is_O_at_top_of_div_tends_to_finite 
  {𝕜 α : Type*} [linear_order α] [nonempty α] [normed_linear_ordered_field 𝕜]
  {f g : α → 𝕜} (hgf : ∀ᶠ x in filter.at_top, g x = 0 → f x = 0)
  (c : 𝕜) (h : filter.tendsto (f / g) filter.at_top (nhds c)) :
  is_O f g filter.at_top :=
begin
  rw is_O_at_top_iff,
  use (∥c∥ + 1),
  rw filter.tendsto_iff_eventually at h,
  let h' := @h (λ (x : 𝕜), ∥x∥ ≤ ∥c∥ + 1) begin
    rw filter.eventually_iff_exists_mem,
    refine ⟨metric.ball c 1, metric.ball_mem_nhds c zero_lt_one, λ y hy, _⟩,
    exact norm_le_norm_add_const_of_dist_le (le_of_lt hy),
  end,
  rw filter.eventually_at_top at h' hgf,
  obtain ⟨x₀, h⟩ := hgf,
  obtain ⟨x₀', h'⟩ := h',
  refine ⟨max x₀ x₀', λ x hx, _⟩,
  rw max_le_iff at hx,
  specialize h x hx.1,
  specialize h' x hx.2,
  simp only [pi.div_apply, normed_field.norm_div] at h',
  by_cases hfx : f x = 0,
  { have : ∥f x∥ = 0 := trans (congr_arg _ hfx) norm_zero,
    refine this.symm ▸ mul_nonneg (by simpa [hfx] using h') (norm_nonneg (g x)) },
  { replace h := (mt h) hfx,
    rwa div_le_iff _ at h',
    refine lt_of_le_of_ne (norm_nonneg (g x)) (λ h', h _),
    refine norm_eq_zero.mp h'.symm }
end

lemma polynomial_exists_max_root {α : Type*} [integral_domain α]
  [linear_order α]
  (p : polynomial α) (hp : p ≠ 0) :
  ∃ x₀, ∀ x, p.is_root x → x ≤ x₀ :=
begin
  by_cases h : list.maximum (multiset.to_list p.roots) = none,
  { rw list.maximum_eq_none at h,
    refine ⟨0, λ a _, _⟩,
    have : a ∈ (multiset.to_list p.roots),
    by rwa [multiset.mem_to_list, polynomial.mem_roots hp],
    rw h at this,
    refine absurd this (list.not_mem_nil a) },
  { rw [← ne.def, option.ne_none_iff_exists] at h,
    obtain ⟨x₀, hx₀⟩ := h,
    refine ⟨x₀, λ x hx, list.le_maximum_of_mem _ hx₀.symm⟩,
    rwa [multiset.mem_to_list, polynomial.mem_roots hp] }
end

lemma polynomial.eventually_no_roots {𝕜 : Type*} [normed_linear_ordered_field 𝕜]
  (p : polynomial 𝕜) (hp : p ≠ 0) :
  ∀ᶠ x in filter.at_top, ¬ p.is_root x :=
begin
  obtain ⟨x₀, hx₀⟩ := polynomial_exists_max_root p hp,
  rw filter.eventually_at_top,
  refine ⟨x₀ + 1, λ x hx h, _⟩,
  refine absurd (hx₀ x h) (not_le.mpr (lt_of_lt_of_le (lt_add_one x₀) hx)),
end

lemma eventually_of_imp {α : Type*} {p q : α → Prop} {l : filter α}
  (hpq : ∀ x, p x → q x) (h : ∀ᶠ x in l, p x) : ∀ᶠ x in l, q x :=
filter.mem_sets_of_superset h hpq

lemma polynomial.ne_zero_of_degree_ge_degree {R : Type*} [semiring R]
  {p q : polynomial R} (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
polynomial.ne_zero_of_degree_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr
  (by rwa [ne.def, polynomial.degree_eq_bot])) hpq : q.degree > ⊥)

theorem polynomial.is_O_of_degree_le {𝕜 : Type*} [normed_linear_ordered_field 𝕜] [order_topology 𝕜]
  (p : polynomial 𝕜) (q : polynomial 𝕜) (h : p.degree ≤ q.degree) :
  is_O (λ x, polynomial.eval x p) (λ x, polynomial.eval x q) filter.at_top :=
begin
  by_cases hp : p = 0,
  { simpa [hp] using is_O_zero (λ x, polynomial.eval x q) filter.at_top },
  { have hq : q ≠ 0 := polynomial.ne_zero_of_degree_ge_degree h hp,
    cases le_iff_lt_or_eq.mp h with h h,
    { have := polynomial.div_tendsto_zero_of_degree_lt p q h,
      refine is_O_at_top_of_div_tends_to_finite _ 0 this,
      refine eventually_of_imp _ (q.eventually_no_roots hq),
      refine λ x hx hx', absurd hx' hx },
    { have := polynomial.div_tendsto_leading_coeff_div_of_degree_eq p q h,
      refine is_O_at_top_of_div_tends_to_finite _ _ this,
      refine eventually_of_imp _ (q.eventually_no_roots hq),
      refine λ x hx hx', absurd hx' hx } }
end

end to_mathlib

section poly_growth
open polynomial

/-- Predicate for functions that have polynomial growth -/
def poly_growth {β : Type u} [semiring β] [preorder β] [has_norm β] (f : β → β) :=
∃ (p : polynomial β), is_O f (λ a, eval a p) filter.at_top

variables {β : Type u} [semiring β] [preorder β] [has_norm β]

@[simp] lemma poly_growth_const (b : β) : poly_growth (λ _, b) :=
⟨C b, is_O_of_le filter.at_top (λ x, by simp)⟩

@[simp] lemma poly_growth_one : poly_growth (1 : β → β) :=
poly_growth_const 1

@[simp] lemma poly_growth_zero : poly_growth (0 : β → β) :=
poly_growth_const 0

@[simp] lemma poly_growth_id : poly_growth (id : β → β) :=
⟨X, is_O_of_le filter.at_top (λ x, by simp)⟩

variables {𝕜 : Type u} [normed_linear_ordered_field 𝕜] [order_topology 𝕜]

lemma poly_growth_iff_is_O_monomial (f : 𝕜 → 𝕜) :
  poly_growth f ↔ ∃ (n : ℕ), is_O f (λ b, b ^ n) filter.at_top :=
⟨λ h, let ⟨p, hp⟩ := h in ⟨p.nat_degree, is_O.trans hp (is_O.trans
  (is_O_of_degree_le p (X ^ p.nat_degree) (by simp)) 
  (is_O_of_le filter.at_top (λ x, by simp)))⟩, λ h, let ⟨n, hn⟩ := h in 
  ⟨X ^ n, is_O.trans hn (is_O_of_le filter.at_top (λ x, by simp))⟩⟩

lemma poly_growth_add {f g : 𝕜 → 𝕜} (hf : poly_growth f)
  (hg : poly_growth g) : poly_growth (f + g) :=
begin
  obtain ⟨p, hp⟩ := hf,
  obtain ⟨q, hq⟩ := hg,
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

lemma poly_growth_mul {f g : 𝕜 → 𝕜} (hf : poly_growth f)
  (hg : poly_growth g) : poly_growth (f * g) :=
let ⟨p, hp⟩ := hf in let ⟨q, hq⟩ := hg in 
  ⟨p * q, by simpa using is_O.mul hp hq⟩

lemma poly_growth_pow {f : 𝕜 → 𝕜} (hf : poly_growth f) (n : ℕ) :
  poly_growth (f ^ n) :=
begin
  induction n with n hn,
  { refine (pow_zero f) ▸ poly_growth_one },
  { refine (pow_succ f n) ▸ poly_growth_mul hf hn }
end

end poly_growth