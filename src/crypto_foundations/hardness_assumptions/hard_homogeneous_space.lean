/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import algebra.add_torsor
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable
import computational_monads.coercions.sim_oracle
import crypto_foundations.sec_experiment
import computational_monads.distribution_semantics.bool

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space, an extension of a group action
on some set such that the action of each group element defines a bijection.
We use mathlib's `add_torsor` type class to represent the bijection property,
and further extend this with various assumptions about run times of computations.

`algorithmic_homogeneous_space` requires the group operations to be efficiently computable.
`hard_homogeneous_space` further requires vectorization and parallelization are hard.

PAPER: use this to show concrete and asymptotic security bounds.
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec

/-- An `algorithmic_homogenous_space` is a homogenous space where operations are all `poly_time`.
Uses mathlib's definition of an `add_torsor`, which is a bijective group action.
We also assume `G` and `X` are finite types with decidable equality. -/
class algorithmic_homogenous_space (G X : Type) [add_group G] extends add_torsor G X :=
[fintype_G : fintype G] [fintype_X : fintype X]
[inhabited_G : inhabited G] [inhabited_X : inhabited X]
[decidable_eq_G : decidable_eq G] [decidable_eq_X : decidable_eq X]
(poly_time_add : poly_time (λ x, x.1 + x.2 : G × G → G))
(poly_time_inv : poly_time (λ x, -x : G → G))
(poly_time_vadd : poly_time (λ x, x.1 +ᵥ x.2 : G × X → X))
(poly_time_eq_G : poly_time (λ x, x.1 = x.2 : G × G → bool))
(poly_time_eq_X : poly_time (λ x, x.1 = x.2 : X × X → bool))
(poly_time_rnd_G : poly_time_oracle_comp (λ (_ : unit), $ᵗ G))

namespace algorithmic_homogenous_space

variables {G X : Type} [add_group G]

instance fx [h : algorithmic_homogenous_space G X] : fintype X := h.fintype_X
instance fg [h : algorithmic_homogenous_space G X] : fintype G := h.fintype_G
instance ix [h : algorithmic_homogenous_space G X] : inhabited X := h.inhabited_X
instance ig [h : algorithmic_homogenous_space G X] : inhabited G := h.inhabited_G
instance dx [h : algorithmic_homogenous_space G X] : decidable_eq X := h.decidable_eq_X
instance dg [h : algorithmic_homogenous_space G X] : decidable_eq G := h.decidable_eq_G

variable [algorithmic_homogenous_space G X]

/-- An adversary for the vectorization game takes in a pair of base points `(x₁, x₂)`,
and attempts to generate a vectorization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`. -/
def vectorization_adversary (G X : Type) :=
sec_adversary uniform_selecting (X × X) G

namespace vectorization_adversary

/-- Analogue of the game for the discrete logarithm assumption.
The input generator randomly chooses the challenge points for the adversary,
and a result is valid if it is exactly the vectorization of the challenge points. -/
@[simps] noncomputable def vectorization_experiment
  (adv : vectorization_adversary G X) :
  sec_experiment uniform_selecting (X × X) G :=
{ inp_gen := do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, return (x₁, x₂)},
  main := adv.run,
  is_valid := λ ⟨x₁, x₂⟩ g, g = x₁ -ᵥ x₂,
  .. base_oracle_algorithm }

noncomputable def advantage (adv : vectorization_adversary G X) : ℝ≥0∞ :=
adv.vectorization_experiment.advantage

variable (adv : vectorization_adversary G X)

@[simp] lemma run_experiment_eq : adv.vectorization_experiment.run =
  do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, g ← adv.run (x₁, x₂), return ((x₁, x₂), g)} :=
by simp [sec_experiment.run, bind_assoc]

lemma advantage_eq_sum_prob_output : adv.advantage =
  (∑ x₁ x₂, ⁅= x₁ -ᵥ x₂ | adv.run (x₁, x₂)⁆) / (fintype.card X) ^ 2 :=
begin
  rw [advantage, sec_experiment.advantage],
  simp only [vectorization_adversary.run_experiment_eq, vectorization_experiment_is_valid,
    prob_event_uniform_select_fintype_bind_eq_sum, prob_event_bind_return],
  simp only [div_eq_mul_inv, ←finset.sum_mul, mul_assoc, ennreal.inv_pow, ← pow_two],
  congr' 1,
  refine finset.sum_congr rfl (λ x1 _, finset.sum_congr rfl (λ x2 _, _)),
  refine prob_event_eq_prob_output _ _ (set.mem_preimage.2 rfl)
    (λ y hy hy', (hy hy').elim)
end

end vectorization_adversary

/-- An adversary for the parallelization game takes in a triple of base points `(x₁, x₂, x₃)`,
and attempts to generate a parralelization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`. -/
def parallelization_adversary (G X : Type) :=
sec_adversary uniform_selecting (X × X × X) X

namespace parallelization_adversary

/-- Analogue of the Computational Diffie-Hellman problem.
The input generator randomly chooses the challenge points for the adversary,
and a result is valid if it is exactly the parallelization of the challenge points. -/
@[simps] noncomputable def parallelization_experiment
  (adv : parallelization_adversary G X) :
  sec_experiment unif_oracle (X × X × X) X :=
{ inp_gen := do
    { x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X,
      return (x₁, x₂, x₃)},
  main := adv.run,
  is_valid := λ ⟨x₁, x₂, x₃⟩ x₄, x₂ -ᵥ x₁ = x₄ -ᵥ x₃,
  .. base_oracle_algorithm }

/-- A `parallelization_adversary` advantage at the experiment. -/
noncomputable def advantage (adv : parallelization_adversary G X) : ℝ≥0∞ :=
adv.parallelization_experiment.advantage

variable (adv : parallelization_adversary G X)

@[simp] lemma run_experiment_eq : adv.parallelization_experiment.run =
  do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X,
    x₄ ← adv.run (x₁, x₂, x₃), return ((x₁, x₂, x₃), x₄)} :=
by simp [sec_experiment.run, bind_assoc]

end parallelization_adversary

/-- Takes in a set of four base points in `X`, attempting to decide if the fourth point
is the correct parallelization of the first three points. -/
def decisional_parallelization_adversary (G X : Type) :=
sec_adversary uniform_selecting (X × X × X × X) bool

namespace decisional_parallelization_adversary

noncomputable def fair_decision_challenge
  (adv : decisional_parallelization_adversary G X) :
  oracle_comp uniform_selecting bool := do
{ x₀ ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G,
  adv.run (x₀, g₁ +ᵥ x₀, g₂ +ᵥ x₀, g₂ +ᵥ (g₁ +ᵥ x₀)) }

noncomputable def unfair_decision_challenge
  (adv : decisional_parallelization_adversary G X) :
  oracle_comp uniform_selecting bool := do
{ x₀ ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G, g₃ ←$ᵗ G,
  adv.run (x₀, g₁ +ᵥ x₀, g₂ +ᵥ x₀, g₃ +ᵥ x₀) }

/-- Analogue of the Decisional Diffie-Hellman problem. -/
@[simps] noncomputable def decisional_parallelization_experiment
  (adv : decisional_parallelization_adversary G X) :
  sec_experiment unif_oracle bool bool :=
{ inp_gen := $ᵗ bool,
  main := λ b, if b then adv.fair_decision_challenge
    else adv.unfair_decision_challenge,
  is_valid := (=),
  .. base_oracle_algorithm }

/-- A `decisional_parallelization_adversary` advantage at the experiment. -/
noncomputable def advantage (adv : decisional_parallelization_adversary G X) : ℝ≥0∞ :=
adv.decisional_parallelization_experiment.advantage

variables (adv : decisional_parallelization_adversary G X)

@[simp] lemma run_experiment_eq : adv.decisional_parallelization_experiment.run =
  do {b ←$ᵗ bool, b' ← if b then adv.fair_decision_challenge
    else adv.unfair_decision_challenge, return (b, b')} :=
by simp [sec_experiment.run]

lemma advantage_eq_prob_output_add_prob_output :
  adv.advantage = (⁅= tt | fair_decision_challenge adv⁆ +
    ⁅= ff | unfair_decision_challenge adv⁆) / 2 :=
begin
  rw [advantage, sec_experiment.advantage],
  simp only [decisional_parallelization_experiment_is_valid],
  rw [prob_event_fst_eq_snd_eq_sum],
  simp only [fintype.univ_bool, finset.sum_insert, finset.mem_singleton, not_false_iff, finset.sum_singleton],
  rw [run_experiment_eq],
  simp_rw [prob_output_uniform_select_bool_bind,
    coe_sort_tt, coe_sort_ff, if_true, if_false],
  simp,
  -- simp [sec_experiment.advantage],

  -- rw [decisional_parallelization_adversary.advantage,
  --   decisional_parallelization_experiment, prob_output_uniform_select_bool_bind],
  -- simp [coe_sort_tt, if_true, ← bind_assoc],
  -- congr' 2,
  -- rw_dist_equiv [bind_const_dist_equiv, bind_return_dist_equiv]
end

end decisional_parallelization_adversary

end algorithmic_homogenous_space

open algorithmic_homogenous_space

/-- A `hard_homogenous_space` is an indexed set of `algorithmic_homogenous_space` such that both
vectorization and parallelization become hard as the index becomes large. -/
class hard_homogenous_space (G X : ℕ → Type) [∀ sp, add_comm_group (G sp)]
  [∀ sp, algorithmic_homogenous_space (G sp) (X sp)] :=
(vectorization_hard : ∀ (adversary : Π sp, vectorization_adversary (G sp) (X sp)),
  negligable (λ sp, (adversary sp).advantage))
(parallelization_hard : ∀ (adversary : Π (sp : ℕ), parallelization_adversary (G sp) (X sp)),
  negligable (λ sp, (adversary sp).advantage))