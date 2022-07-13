import computational_monads.asymptotics.polynomial_time
import computational_monads.coercions
-- import to_mathlib.action_classes
import algebra.add_torsor

open_locale nnreal ennreal

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space.

`algorithmic_homogeneous_space` requires the group action and group operations are efficiently computable.
`hard_homogeneous_space` further requires vectorization and parallelization are hard.
-/

open oracle_comp oracle_spec

/-- An `algorithmic_homogenous_space` is a homogenous space where operations are all `poly_time`.
  Uses mathlib's definition of an `add_torsor`, which is a bijective group action -/
class algorithmic_homogenous_space (G X : Type) [fintype G] [fintype X]
  [decidable_eq G] [decidable_eq X] [add_group G] extends add_torsor G X :=
(poly_time_add : poly_time (λ x, x.1 + x.2 : G × G → G))
(poly_time_inv : poly_time (λ x, -x : G → G))
(poly_time_vadd : poly_time (λ x, x.1 +ᵥ x.2 : G × X → X))
(poly_time_eq_G : poly_time (λ x, x.1 = x.2 : G × G → bool))
(poly_time_eq_X : poly_time (λ x, x.1 = x.2 : X × X → bool))
(poly_time_rnd_G : poly_time_oracle_comp (λ (_ : unit), $ᵗ G)) 

section computational_advantages

variables {G X : Type} [fintype G] [fintype X] [decidable_eq G] [decidable_eq X]
  [add_group G] [algorithmic_homogenous_space G X]
  
namespace vectorization

structure adversary (G X : Type) : Type 1 :=
(adv : X × X → oracle_comp uniform_selecting G)
(adv_poly_time : poly_time_oracle_comp adv)

section naive_adversary

variables (G X)

noncomputable def naive_adversary : adversary G X :=
{ adv := λ _, $ᵗ G,
  adv_poly_time := sorry }

end naive_adversary

/-- Analogue of Discrete-logarithm asumption game -/
noncomputable def experiment (adversary : adversary G X) : oracle_comp uniform_selecting bool :=
do{ x₁ ←$ᵗ X, x₂ ←$ᵗ X,
    g ← adversary.adv (x₁, x₂),
    return (g = x₁ -ᵥ x₂) }

/-- Vectorization advantage of an adversary in the vectorization experiment. -/
noncomputable def advantage (adversary : adversary G X) : ℝ≥0∞ :=
⦃ (=) tt | experiment adversary ⦄ - ⦃ (=) tt | experiment (naive_adversary G X) ⦄

end vectorization

namespace parallelization

structure adversary (G X : Type) :=
(adv : X × X × X → oracle_comp uniform_selecting X)
(adv_poly_time : poly_time_oracle_comp adv)

section naive_adversary

variables (G X)

noncomputable def naive_adversary : adversary G X :=
{ adv := λ _, $ᵗ X,
  adv_poly_time := sorry }

end naive_adversary

/-- Analogue of the decisional Diffie-Helman experiment -/
noncomputable def experiment (adversary : adversary G X) :
  oracle_comp uniform_selecting bool :=
do{ x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X,
    x₄ ← adversary.adv (x₁, x₂, x₃),
    return (x₂ -ᵥ x₁ = x₄ -ᵥ x₃) }

/-- Parallelization advantage of an adversary in parallelization experiment -/
noncomputable def advantage (adversary : adversary G X) :
  ℝ≥0∞ :=
⦃ (=) tt | experiment adversary ⦄ - ⦃ (=) tt | experiment (naive_adversary G X) ⦄

end parallelization

end computational_advantages

/-- A `hard_homogenous_space` is a -/
class hard_homogenous_space {G X : ℕ → Type} [∀ n, fintype $ G n] [∀ n, fintype $ X n]
  [∀ n, decidable_eq $ G n] [∀ n, decidable_eq $ X n]
  [∀ n, add_group $ G n] [∀ n, algorithmic_homogenous_space (G n) (X n)] :=
(vectorization_hard : ∀ (adversary : Π (sp : ℕ), vectorization.adversary (G sp) (X sp)),
  negligable (λ sp, vectorization.advantage (adversary sp)))
(parallelization_hard : ∀ (adversary : Π (sp : ℕ), parallelization.adversary (G sp) (X sp)),
  negligable (λ sp, parallelization.advantage (adversary sp)))
