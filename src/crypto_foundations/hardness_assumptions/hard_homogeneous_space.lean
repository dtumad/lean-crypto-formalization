import computational_monads.asymptotics.polynomial_time
import computational_monads.coercions
import to_mathlib.action_classes

open_locale nnreal ennreal

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space.

`algorithmic_homogeneous_space` requires the group action and group operations are efficiently computable.
`hard_homogeneous_space` further requires vectorization and parallelization are hard.
-/

open oracle_comp oracle_spec

class algorithmic_homogenous_space (G X : Type) [fintype G] [fintype X] [inhabited X]
  [add_group G] [add_action G X] [decidable_eq G] [decidable_eq X]
  extends principal_action_class G X :=
(poly_time_add : poly_time (λ x, x.1 + x.2 : G × G → G))
(poly_time_inv : poly_time (λ x, -x : G → G))
(poly_time_vadd : poly_time (λ x, x.1 +ᵥ x.2 : G × X → X))
(poly_time_eq_G : poly_time (λ x, x.1 = x.2 : G × G → bool))
(poly_time_eq_X : poly_time (λ x, x.1 = x.2 : X × X → bool))
(poly_time_rnd_G : poly_time_oracle_comp (λ _, uniform_select_fintype G : unit → oracle_comp oracle_spec.uniform_selecting G)) 

section computational_advantages

variables {G X : Type} [fintype G] [fintype X] [inhabited X]
  [add_group G] [add_action G X]
  [decidable_eq G] [decidable_eq X]
  [principal_action_class G X]
  
-- instance to_principal_action_class : principal_action_class G X :=

/-- Analogue of Discrete-logarithm asumption game -/
noncomputable def vectorization_experiment (adversary : X × X → oracle_comp uniform_selecting G) :
  oracle_comp uniform_selecting bool :=
do{ x₁ ←$ᵗ X, x₂ ←$ᵗ X,
    g ← adversary (x₁, x₂),
    return (g = vectorization G x₁ x₂) }

/-- Vectorization advantage of an adversary in the vectorization experiment. -/
noncomputable def vectorization_advantage (adversary : X × X → oracle_comp uniform_selecting G) :
  ℝ≥0∞ :=
⟦ (=) tt | vectorization_experiment adversary ⟧
  - ⟦ (=) tt | vectorization_experiment (λ (_ : X × X), $ᵗ G) ⟧

variable (G)

/-- Analogue of the decisional Diffie-Helman experiment -/
noncomputable def parallelization_experiment (adversary : X × X × X → oracle_comp uniform_selecting X) :
  oracle_comp uniform_selecting bool :=
do{ x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X,
    x₄ ← adversary (x₁, x₂, x₃),
    return ((vectorization G x₂ x₁) = (vectorization G x₄ x₃)) }

/-- Parallelization advantage of an adversary in parallelization experiment -/
noncomputable def parallelization_advantage (adversary : X × X × X → oracle_comp uniform_selecting X) :
  ℝ≥0∞ :=
⟦ (=) tt | parallelization_experiment G adversary ⟧
  - ⟦ (=) tt | parallelization_experiment G (λ _, $ᵗ X) ⟧

end computational_advantages

-- TODO: the algorithmic stuff is kinda weird here?
class hard_homogenous_space {G X : ℕ → Type} 
  [∀ n, fintype $ G n] [∀ n, fintype $ X n] [∀ n, inhabited $ X n]
  [∀ n, add_group $ G n] [∀ n, add_action (G n) (X n)]
  [∀ n, decidable_eq $ G n] [∀ n, decidable_eq $ X n]
  [∀ n, algorithmic_homogenous_space (G n) (X n)] :=
-- (algorithmic : ∀ n, algorithmic_homogenous_space (G n) (X n))
(vectorization_hard : ∀ (adversary : Π (n : ℕ), X n × X n → oracle_comp uniform_selecting (G n))
  (poly_time : ∀ n, poly_time_oracle_comp $ adversary n),
  negligable (λ n, vectorization_advantage (adversary n)))
(parallelization_hard : ∀ (adversary : Π (n : ℕ), X n × X n × X n → oracle_comp uniform_selecting (X n))
  (poly_time : ∀ n, poly_time_oracle_comp $ adversary n),
  negligable (λ n, parallelization_advantage (G n) (adversary n)))
