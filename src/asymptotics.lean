import comp
import to_mathlib
import analysis.asymptotics.asymptotics

open asymptotics

instance norm_nat : has_norm ℕ :=
{ norm := λ n, ↑n }

@[simp] lemma norm_nat_def {n : ℕ} : ∥n∥ = (n : ℝ) := rfl

theorem nat_is_O_iff {f g : ℕ → ℕ} :
  is_O f g filter.at_top ↔ ∃ c C, ∀ x, C ≤ x → f x ≤ c * (g x) :=
begin
  simp only [is_O_iff, filter.eventually_at_top, norm_nat_def],
  refine ⟨_, λ h, let ⟨c, C, h⟩ := h in
      ⟨c, C, λ n hn, trans (nat.cast_le.mpr (h n hn)) (le_of_eq (nat.cast_mul _ _))⟩⟩,
  rintro ⟨c, C, h⟩,
  obtain ⟨c', hc'⟩ := exists_nat_ge c,
  refine ⟨c', C, λ n hn, _⟩,
  have : (f n : ℝ) ≤ ↑(c' * g n) := trans (h n hn) (by simpa using 
    mul_le_mul hc' (le_refl (g n)) (nat.cast_nonneg (g n)) (nat.cast_nonneg c')),
  refine nat.cast_le.mp this,    
end

