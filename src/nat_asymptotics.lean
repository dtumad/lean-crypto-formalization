import analysis.asymptotics.asymptotics
import data.polynomial
import data.real.nnreal
import analysis.special_functions.polynomials

universes u v

open_locale nnreal

-- Most of this file should eventually be ported to mathlib probably

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

lemma is_O_at_top_add {f f' g : ℚ → ℚ} (hf : is_O f g filter.at_top)
  (hf' : is_O f' g filter.at_top) : (is_O (f + f') g filter.at_top) :=
begin
  rw is_O_at_top_iff at hf hf' ⊢,
  obtain ⟨M, x₀, hf⟩ := hf,
  obtain ⟨M', x₀', hf'⟩ := hf',
  refine ⟨M + M', max x₀ x₀', λ x hx, _⟩,
  rw max_le_iff at hx,
  rw [pi.add_apply, add_mul],
  refine trans (norm_add_le (f x) (f' x)) _,
  refine add_le_add (hf x hx.1) (hf' x hx.2),
end

end is_O_at_top

lemma norm_le_norm_add_const_of_dist_le {α : Type u} [normed_group α]
  {a b : α} {c : ℝ} (h : dist a b ≤ c) : ∥a∥ ≤ ∥b∥ + c :=
calc ∥a∥ = ∥a - b + b∥ : by rw sub_add_cancel a b
    ... ≤ ∥a - b∥ + ∥b∥ : norm_add_le (a - b) b
    ... = (dist a b) + ∥b∥ : by rw normed_group.dist_eq
    ... ≤ c + ∥b∥ : add_le_add h le_rfl
    ... ≤ ∥b∥ + c : by rw (add_comm c ∥b∥)

example {a b : ℚ} : a / b ≠ 0 → b ≠ 0 :=
begin
  contrapose!,
  refine λ h, _,
  rw h,
  simp,
end

theorem is_O_at_top_of_div_tends_to_finite {f g : ℚ → ℚ} 
  (hgf : ∀ᶠ x in filter.at_top, g x = 0 → f x = 0)
  (c : ℚ) (h : filter.tendsto (f / g) filter.at_top (nhds c)) :
  is_O f g filter.at_top :=
begin
  rw is_O_at_top_iff,
  use (∥c∥ + 1),
  rw filter.tendsto_iff_eventually at h,
  have h' := @h (λ (x : ℚ), ∥x∥ ≤ ∥c∥ + 1) begin
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

lemma polynomial_exists_max_root (p : polynomial ℚ) (hp : p ≠ 0) :
  ∃ x₀, ∀ x, p.is_root x → x ≤ x₀ :=
begin
  let rootsl : list ℚ := multiset.to_list p.roots,
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

lemma polynomial.eventually_no_roots (p : polynomial ℚ) (hp : p ≠ 0) :
  ∀ᶠ x in filter.at_top, ¬ p.is_root x :=
begin
  obtain ⟨x₀, hx₀⟩ := polynomial_exists_max_root p hp,
  rw filter.eventually_at_top,
  refine ⟨x₀ + 1, λ x hx h, _⟩,
  specialize hx₀ x h,
  refine absurd hx₀ _,
  rw not_le,
  refine lt_of_lt_of_le _ hx,
  rw lt_add_iff_pos_right,
  refine zero_lt_one,  
end

lemma eventually_imp_help {p q : ℚ → Prop} {l : filter ℚ}
  (hpq : ∀ x, p x → q x) (h : ∀ᶠ x in l, p x) : 
  ∀ᶠ x in l, q x :=
filter.mem_sets_of_superset h hpq

theorem polynomial.is_O_iff_degree_le (p : polynomial ℚ) (q : polynomial ℚ)
  (h : p.degree ≤ q.degree) :
  is_O (λ x, polynomial.eval x p) (λ x, polynomial.eval x q) filter.at_top :=
begin
  by_cases hp : p = 0,
  { simpa [hp] using is_O_zero (λ x, polynomial.eval x q) filter.at_top },
  { have hq : q ≠ 0 := begin
      refine λ hq, hp _,
      rw ← polynomial.degree_eq_bot at hp ⊢,
      refine eq_bot_iff.mpr (trans h (eq_bot_iff.mp _)),
      rwa polynomial.degree_eq_bot,
    end,
    rw le_iff_lt_or_eq at h,
    cases h,
    { have := polynomial.div_tendsto_zero_of_degree_lt p q h,
      refine is_O_at_top_of_div_tends_to_finite _ 0 this,
      refine eventually_imp_help _ (q.eventually_no_roots hq),
      refine λ x hx hx', absurd hx' hx,
      },
    { have := polynomial.div_tendsto_leading_coeff_div_of_degree_eq p q h,
      refine is_O_at_top_of_div_tends_to_finite _ _ this,
      refine eventually_imp_help _ (q.eventually_no_roots hq),
      refine λ x hx hx', absurd hx' hx,
      },
  }
end

variables {α β : Type*}

/-- Predicate for functions that have polynomial growth -/
def poly_growth [semiring β] [preorder α] [has_norm α] [has_norm β] 
  [has_lift_t α β] (f : α → β) := 
∃ (p : polynomial β), is_O f (λ (a : α), polynomial.eval ↑a p) filter.at_top

end nat_asymptotics