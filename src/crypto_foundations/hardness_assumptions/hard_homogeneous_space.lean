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
Uses mathlib's definition of an `add_torsor`, which is a bijective group action.
We also assume `G` and `X` are finite types with decidable equality. -/
class algorithmic_homogenous_space (G X : Type) extends add_group G, add_torsor G X :=
[fintype_G : fintype G] [fintype_X : fintype X]
[decidable_eq_G : decidable_eq G] [decidable_eq_X : decidable_eq X]
(poly_time_add : poly_time (λ x, x.1 + x.2 : G × G → G))
(poly_time_inv : poly_time (λ x, -x : G → G))
(poly_time_vadd : poly_time (λ x, x.1 +ᵥ x.2 : G × X → X))
(poly_time_eq_G : poly_time (λ x, x.1 = x.2 : G × G → bool))
(poly_time_eq_X : poly_time (λ x, x.1 = x.2 : X × X → bool))
(poly_time_rnd_G : poly_time_oracle_comp (λ (_ : unit), $ᵗ G))

namespace algorithmic_homogenous_space

variables {G X : Type} [algorithmic_homogenous_space G X]

instance fx [h : algorithmic_homogenous_space G X] : fintype X := h.fintype_X
instance fg [h : algorithmic_homogenous_space G X] : fintype G := h.fintype_G
instance dx [h : algorithmic_homogenous_space G X] : decidable_eq X := h.decidable_eq_X
instance dg [h : algorithmic_homogenous_space G X] : decidable_eq G := h.decidable_eq_G

/-- An adversary for the vectorization game takes in a pair of base points `(x₁, x₂)`,
and attempts to generate a vectorization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`. -/
structure vectorization_adversary (G X : Type) [algorithmic_homogenous_space G X]
  extends sec_adversary uniform_selecting (X × X) G

/-- Analogue of the game for the discrete logarithm assumption.
The input generator randomly chooses the challenge points for the adversary,
and a result is valid if it is exactly the vectorization of the challenge points. -/
noncomputable def vectorization_experiment (G X : Type) [algorithmic_homogenous_space G X] :
  sec_experiment uniform_selecting (X × X) G unit unit :=
{ inp_gen := ($ᵗ X ×ₘ $ᵗ X) ×ₘ return (),
  is_valid := λ ⟨x₁, x₂⟩ ⟨g, u⟩, return (g = x₁ -ᵥ x₂) }

/-- An adversary for the parallelization game takes in a triple of base points `(x₁, x₂, x₃)`,
and attempts to generate a parralelization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`. -/
structure parallelization_adversary (G X : Type) [algorithmic_homogenous_space G X]
  extends sec_adversary uniform_selecting (X × X × X) X

/-- Analogue of the computational discrete logarithm problem.
The input generator randomly chooses the challenge points for the adversary,
and a result is valid if it is exactly the parallelization of the challenge points. -/
noncomputable def parallelization_experiment (G X : Type) [algorithmic_homogenous_space G X] :
  sec_experiment uniform_selecting (X × X × X) X unit unit :=
{ inp_gen := ($ᵗ X ×ₘ $ᵗ X ×ₘ $ᵗ X) ×ₘ return (),
  is_valid := λ ⟨x₁, x₂, x₃⟩ ⟨x₄, u⟩, return (x₂ -ᵥ x₁ = x₄ -ᵥ x₃) }


-- /-- The adversary's advantage at vectorization is the average over all possible pairs of points
-- of their advantage at vectorizing those specific points. -/
-- lemma advantage_eq_tsum (adv : vectorization_adversary G X) :
--   adv.advantage = (∑' x₁ x₂, ⁅(=) (x₁ -ᵥ x₂) | adv.run (x₁, x₂)⁆) / (fintype.card X) ^ 2 :=
-- calc adv.advantage = ⁅= tt | experiment adv⁆ : rfl
--   ... = ((fintype.card X)⁻¹ ^ 2) * (∑' x₁ x₂, ⁅adv.run (x₁, x₂)⁆ (x₁ -ᵥ x₂)) :
--   begin
--     sorry,

--     -- simp only [experiment, prob_output_bind_eq_tsum ($ᵗ X), pow_two, ← mul_assoc,
--     --   eval_dist_uniform_select_fintype_apply, ennreal.tsum_mul_left],
--     -- refine congr_arg (λ x, _ * x) (tsum_congr (λ x₁, tsum_congr (λ x₂, _))),
--     -- refine (eval_dist_bind_return_apply_eq_single (adversary.adv (x₁, x₂)) _ tt (x₁ -ᵥ x₂)) _,
--     -- simp only [set.preimage, set.mem_singleton_iff, to_bool_iff, set.set_of_eq_eq_singleton],
--   end
--   ... = (∑' x₁ x₂, ⁅adv.run (x₁, x₂)⁆ (x₁ -ᵥ x₂)) / (fintype.card X) ^ 2 :
--     by rw [div_eq_mul_inv, ennreal.inv_pow, mul_comm]
--   ... = (∑' x₁ x₂, ⁅(=) (x₁ -ᵥ x₂) | adv.run (x₁, x₂)⁆) / (fintype.card X) ^ 2 :
--     sorry --by simp_rw [prob_event_eq_eq_prob_output]

end algorithmic_homogenous_space

open algorithmic_homogenous_space

/-- A `hard_homogenous_space` is an indexed set of `algorithmic_homogenous_space` such that both
vectorization and parallelization become hard as the index becomes large. -/
class hard_homogenous_space (G X : ℕ → Type) [∀ n, algorithmic_homogenous_space (G n) (X n)] :=
(vectorization_hard : ∀ (adversary : Π (sp : ℕ), vectorization_adversary (G sp) (X sp)),
  negligable (λ sp, (adversary sp).advantage (vectorization_experiment (G sp) (X sp)) idₛₒ))
(parallelization_hard : ∀ (adversary : Π (sp : ℕ), parallelization_adversary (G sp) (X sp)),
  negligable (λ sp, (adversary sp).advantage (parallelization_experiment (G sp) (X sp)) idₛₒ))
