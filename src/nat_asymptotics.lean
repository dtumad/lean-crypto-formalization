import analysis.asymptotics.asymptotics
import data.polynomial

section nat_asymptotics
open asymptotics

instance nat.norm : has_norm ℕ :=
{ norm := λ n, ↑n }

@[simp] lemma norm_nat_def {n : ℕ} : ∥n∥ = ↑n := rfl

@[simp] lemma norm_nat_le_iff {n m : ℕ} : 
  ∥n∥ ≤ ∥m∥ ↔ n ≤ m := by simp

theorem nat_is_O_iff {f g : ℕ → ℕ} :
  is_O f g filter.at_top ↔ ∃ M x₀, ∀ x, x₀ ≤ x → f x ≤ M * (g x) :=
begin
  simp only [is_O_iff, filter.eventually_at_top, norm_nat_def],
  refine ⟨_, λ h, let ⟨c, C, h⟩ := h in
      ⟨c, C, λ n hn, trans (nat.cast_le.mpr (h n hn)) (le_of_eq (nat.cast_mul _ _))⟩⟩,
  rintro ⟨c, x₀, h⟩,
  obtain ⟨c', hc'⟩ := exists_nat_ge c,
  refine ⟨c', x₀, λ n hn, _⟩,
  have : (f n : ℝ) ≤ ↑(c' * g n) := trans (h n hn) (by simpa using 
    mul_le_mul hc' (le_refl (g n)) (nat.cast_nonneg (g n)) (nat.cast_nonneg c')),
  refine nat.cast_le.mp this,    
end

theorem nat_is_O_trans {f g h : ℕ → ℕ} (hfg : is_O f g filter.at_top)
  (hgh : is_O g h filter.at_top) : is_O f h filter.at_top :=
begin
  rw nat_is_O_iff at hfg hgh ⊢,
  obtain ⟨M, x₀, hM⟩ := hfg,
  obtain ⟨M', x₀', hM'⟩ := hgh,
  refine ⟨M * M', max x₀ x₀', λ x hx, _⟩,
  rw max_le_iff at hx,
  specialize hM x hx.1,
  specialize hM' x hx.2,
  rw mul_assoc,
  refine trans hM (mul_le_mul le_rfl hM' zero_le' zero_le'),
end

lemma polynomial_is_O_pow_degree (p : polynomial ℕ) :
  is_O (λ x, polynomial.eval x p) (λ x, x ^ p.nat_degree) filter.at_top :=
begin
  rw is_O_iff,
  use ∥ (finsupp.sum p (λ (e : ℕ), id)) ∥,
  rw filter.eventually_at_top,
  use 1,
  intros b hb,
  simp only [norm_nat_def, ← nat.cast_pow, ← nat.cast_mul, nat.cast_le,
    polynomial.eval_eq_sum, finsupp.sum_mul],
  refine finset.sum_le_sum (λ x hx, mul_le_mul le_rfl (pow_le_pow hb 
    (polynomial.le_nat_degree_of_mem_supp x hx)) zero_le' zero_le'),
end

/-- Predicate for functions that have polynomial growth -/
def poly_growth {α : Type*} [semiring α] [has_norm α] [preorder α] (f : α → α) := 
∃ (p : polynomial α), is_O f (λ n, polynomial.eval n p) filter.at_top

theorem poly_growth_iff (f : ℕ → ℕ) :
  poly_growth f ↔ ∃ (m : ℕ), is_O f (λ n, n ^ m) filter.at_top :=
⟨λ h, let ⟨p, hp⟩ := h in ⟨p.nat_degree, nat_is_O_trans hp (polynomial_is_O_pow_degree p)⟩,
  λ h, let ⟨m, hm⟩ := h in ⟨polynomial.X ^ m, by simpa⟩⟩

end nat_asymptotics