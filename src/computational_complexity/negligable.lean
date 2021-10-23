import computational_complexity.polynomial_asymptotics

/-!
# Negligable Growth

This file defines the notion of a negligable function `f : ℕ → ℝ`.
For convenience, the definition is given in terms of `is_O`,
  with various lemmas to translate to definitions in terms of constants
-/

namespace asymptotics

-- TODO: Use superpolynomial decay instead
def negligable (f : ℕ → ℝ) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

end asymptotics