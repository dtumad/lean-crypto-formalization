/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import algebra.add_torsor
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable
import computational_monads.coercions.sim_oracle
import crypto_foundations.sec_adversary

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space, an extension of a group action
on some set such that the action of each group element defines a bijection.
We use mathlib's `add_torsor` type class to represent the bijection property,
and further extend this with various assumptions about run times of computations.

`algorithmic_homogeneous_space` requires the group operations to be efficiently computable.
`hard_homogeneous_space` further requires vectorization and parallelization are hard.
-/

open_locale big_operators ennreal
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

namespace algorithmic_homogenous_space

variables {G X : Type} [fintype G] [fintype X] [decidable_eq G] [decidable_eq X]
  [add_group G] [algorithmic_homogenous_space G X]

structure vectorization_adversary (G X : Type)
  extends sec_adversary uniform_selecting (X × X) G

-- structure vectorization_adversary (G X : Type) : Type 1 :=
-- (adv : X × X → oracle_comp uniform_selecting G) -- TODO: name `adv` -> `alg`?
-- (adv_poly_time : poly_time_oracle_comp adv)

namespace vectorization_adversary

/-- Analogue of Discrete-logarithm asumption game -/
noncomputable def experiment (adv : vectorization_adversary G X) :
  oracle_comp uniform_selecting bool :=
do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, g ← adv.run (x₁, x₂), return (g = x₁ -ᵥ x₂)}

/-- Vectorization advantage of an adversary in the vectorization experiment. -/
noncomputable def advantage (adv : vectorization_adversary G X) : ℝ≥0∞ :=
⁅= tt | experiment adv⁆

/-- The adversary's advantage at vectorization is the average over all possible pairs of points
of their advantage at vectorizing those specific points. -/
lemma advantage_eq_tsum (adv : vectorization_adversary G X) :
  adv.advantage = (∑' x₁ x₂, ⁅(=) (x₁ -ᵥ x₂) | adv.run (x₁, x₂)⁆) / (fintype.card X) ^ 2 :=
calc adv.advantage = ⁅= tt | experiment adv⁆ : rfl
  ... = ((fintype.card X)⁻¹ ^ 2) * (∑' x₁ x₂, ⁅adv.run (x₁, x₂)⁆ (x₁ -ᵥ x₂)) :
  begin
    sorry,

    -- simp only [experiment, prob_output_bind_eq_tsum ($ᵗ X), pow_two, ← mul_assoc,
    --   eval_dist_uniform_select_fintype_apply, ennreal.tsum_mul_left],
    -- refine congr_arg (λ x, _ * x) (tsum_congr (λ x₁, tsum_congr (λ x₂, _))),
    -- refine (eval_dist_bind_return_apply_eq_single (adversary.adv (x₁, x₂)) _ tt (x₁ -ᵥ x₂)) _,
    -- simp only [set.preimage, set.mem_singleton_iff, to_bool_iff, set.set_of_eq_eq_singleton],
  end
  ... = (∑' x₁ x₂, ⁅adv.run (x₁, x₂)⁆ (x₁ -ᵥ x₂)) / (fintype.card X) ^ 2 :
    by rw [div_eq_mul_inv, ennreal.inv_pow, mul_comm]
  ... = (∑' x₁ x₂, ⁅(=) (x₁ -ᵥ x₂) | adv.run (x₁, x₂)⁆) / (fintype.card X) ^ 2 :
    sorry --by simp_rw [prob_event_eq_eq_prob_output]

end vectorization_adversary

namespace parallelization

structure adversary (G X : Type) :=
(adv : X × X × X → oracle_comp uniform_selecting X)
(adv_poly_time : poly_time_oracle_comp adv)

/-- Analogue of the decisional Diffie-Helman experiment -/
noncomputable def experiment (adversary : adversary G X) :
  oracle_comp uniform_selecting bool :=
do{ x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X, x₄ ← adversary.adv (x₁, x₂, x₃), return (x₂ -ᵥ x₁ = x₄ -ᵥ x₃) }

/-- Parallelization advantage of an adversary in parallelization experiment -/
noncomputable def advantage (adversary : adversary G X) : ℝ≥0∞ :=
⁅ (=) tt | experiment adversary ⁆

end parallelization

end algorithmic_homogenous_space

open algorithmic_homogenous_space

/-- A `hard_homogenous_space` is a -/
class hard_homogenous_space (G X : ℕ → Type) [∀ n, fintype $ G n] [∀ n, fintype $ X n]
  [∀ n, decidable_eq $ G n] [∀ n, decidable_eq $ X n]
  [∀ n, add_group $ G n] [∀ n, algorithmic_homogenous_space (G n) (X n)] :=
(vectorization_hard : ∀ (adversary : Π (sp : ℕ), vectorization_adversary (G sp) (X sp)),
  negligable (λ sp, (adversary sp).advantage ))
(parallelization_hard : ∀ (adversary : Π (sp : ℕ), parallelization.adversary (G sp) (X sp)),
  negligable (λ sp, parallelization.advantage (adversary sp)))
