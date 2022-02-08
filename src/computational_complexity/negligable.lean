import computational_complexity.polynomial_asymptotics
import analysis.asymptotics.superpolynomial_decay

open_locale topological_space
open filter

/-!
# Negligable Growth

This file defines the notion of a negligable function `f : ℕ → ℝ`.
For convenience, the definition is given in terms of `is_O`,
  with various lemmas to translate to definitions in terms of constants
-/

namespace asymptotics

-- TODO: Use superpolynomial decay instead
def negligable (f : ℕ → ℝ) := superpolynomial_decay at_top coe f

end asymptotics