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
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec

/-- An `algorithmic_homogenous_space` is a homogenous space where operations are all `poly_time`.
Uses mathlib's definition of an `add_torsor`, which is a bijective group action.
We also assume `G` and `X` are finite types with decidable equality. -/
class algorithmic_homogenous_space (G X : Type)
  [add_comm_group G] extends add_torsor G X :=
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

variables {G X : Type} [add_comm_group G]

instance fx [h : algorithmic_homogenous_space G X] : fintype X := h.fintype_X
instance fg [h : algorithmic_homogenous_space G X] : fintype G := h.fintype_G
instance ix [h : algorithmic_homogenous_space G X] : inhabited X := h.inhabited_X
instance ig [h : algorithmic_homogenous_space G X] : inhabited G := h.inhabited_G
instance dx [h : algorithmic_homogenous_space G X] : decidable_eq X := h.decidable_eq_X
instance dg [h : algorithmic_homogenous_space G X] : decidable_eq G := h.decidable_eq_G

variable [algorithmic_homogenous_space G X]

def equiv (G X : Type) [add_comm_group G] [algorithmic_homogenous_space G X] :
  G ≃ X := ⟨λ g, g +ᵥ default, λ x, x -ᵥ default, λ g, vadd_vsub _ _, λ x, vsub_vadd _ _⟩

lemma card_eq_card (G X : Type) [add_comm_group G] [algorithmic_homogenous_space G X] :
  fintype.card G = fintype.card X :=
fintype.card_congr (algorithmic_homogenous_space.equiv G X)

lemma vadd_bijective (x : X) : function.bijective (λ g, g +ᵥ x : G → X) :=
begin
  refine ⟨λ g g' h, _, λ x', ⟨x' -ᵥ x, vsub_vadd _ _⟩⟩,
  simpa only [vadd_right_cancel_iff] using h,
end

lemma vsub_bijective (x : X) : function.bijective (λ x', x' -ᵥ x : X → G) :=
begin
  refine ⟨λ x' x'' h, _, λ g, ⟨g +ᵥ x, vadd_vsub _ _⟩⟩,
  simpa only [vsub_left_cancel_iff] using h,
end

/-- An adversary for the vectorization game takes in a pair of base points `(x₁, x₂)`,
and attempts to generate a vectorization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`. -/
def vectorization_adv (G X : Type) :=
sec_adv unif_spec (X × X) G

/-- Analogue of the game for the discrete logarithm assumption.
The input generator randomly chooses the challenge points for the adversary,
and a result is valid if it is exactly the vectorization of the challenge points. -/
noncomputable def vectorization_exp (adv : vectorization_adv G X) :
  sec_exp unif_spec (X × X) G :=
{ inp_gen := do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, return (x₁, x₂)},
  main := adv.run,
  is_valid := λ ⟨x₁, x₂⟩ g, g = x₁ -ᵥ x₂,
  .. base_oracle_algorithm }

namespace vectorization_exp

variables (adv : vectorization_adv G X)

@[simp] lemma inp_gen_eq : (vectorization_exp adv).inp_gen =
  do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, return (x₁, x₂)} := rfl

@[simp] lemma main_eq : (vectorization_exp adv).main  = adv.run := rfl

@[simp] lemma is_valid_eq : (vectorization_exp adv).is_valid =
  λ xs g, g = xs.1 -ᵥ xs.2 := funext (λ xs, by cases xs; refl)

@[simp] lemma exec_eq : (vectorization_exp adv).to_oracle_algorithm = base_oracle_algorithm := rfl

@[simp] lemma run_eq : (vectorization_exp adv).run =
  do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, g ← adv.run (x₁, x₂), return ((x₁, x₂), g)} :=
by simp [sec_exp.run, bind_assoc]

lemma advantage_eq_sum : (vectorization_exp adv).advantage =
  (∑ x₁ x₂, ⁅= x₁ -ᵥ x₂ | adv.run (x₁, x₂)⁆) / (fintype.card X) ^ 2 :=
by simp only [sec_exp.advantage, div_eq_mul_inv, ←finset.sum_mul, mul_assoc, ennreal.inv_pow,
  ← pow_two, vectorization_exp.run_eq, vectorization_exp.is_valid_eq, prob_event_bind_return,
  prob_event_uniform_select_fintype_bind_eq_sum, function.comp, prob_event_eq_eq_prob_output']

lemma advantage_eq_tsum : (vectorization_exp adv).advantage =
  (∑' x₁ x₂, ⁅= x₁ -ᵥ x₂ | adv.run (x₁, x₂)⁆) / (fintype.card X) ^ 2 :=
begin
  rw [advantage_eq_sum],
  refine congr_arg (λ r : ℝ≥0∞, r / ((fintype.card X) ^ 2)) _,
  refine trans (symm (tsum_eq_sum (λ _ h, (h (finset.mem_univ _)).elim))) _,
  refine tsum_congr (λ x₁, _),
  refine (symm (tsum_eq_sum (λ _ h, (h (finset.mem_univ _)).elim))),
end

end vectorization_exp

/-- An adversary for the parallelization game takes in a triple of base points `(x₁, x₂, x₃)`,
and attempts to generate a parralelization, i.g. a vector `g` with `g +ᵥ x₂ = x₁`. -/
def parallelization_adv (G X : Type) :=
sec_adv unif_spec (X × X × X) X

/-- Analogue of the Computational Diffie-Hellman problem.
The input generator randomly chooses the challenge points for the adversary,
and a result is valid if it is exactly the parallelization of the challenge points. -/
noncomputable def parallelization_exp (adv : parallelization_adv G X) :
  sec_exp unif_spec (X × X × X) X :=
{ inp_gen := do
    { x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X,
      return (x₁, x₂, x₃) },
  main := adv.run,
  is_valid := λ ⟨x₁, x₂, x₃⟩ x₄, x₂ -ᵥ x₁ = x₄ -ᵥ x₃,
  .. base_oracle_algorithm }

namespace parallelization_exp

variable (adv : parallelization_adv G X)

@[simp] lemma inp_gen_eq : (parallelization_exp adv).inp_gen =
  do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X, return (x₁, x₂, x₃)} := rfl

@[simp] lemma main_eq : (parallelization_exp adv).main = adv.run := rfl

@[simp] lemma is_valid_eq : (parallelization_exp adv).is_valid =
  λ xs x₄, xs.2.1 -ᵥ xs.1 = x₄ -ᵥ xs.2.2 := funext (λ xs, by rcases xs with ⟨x₁, x₂, x₃⟩; refl)

@[simp] lemma to_oracle_algorithm_eq : (parallelization_exp adv).to_oracle_algorithm =
  base_oracle_algorithm := rfl

@[simp] lemma run_experiment_eq : (parallelization_exp adv).run =
  do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, x₃ ←$ᵗ X,
    x₄ ← adv.run (x₁, x₂, x₃), return ((x₁, x₂, x₃), x₄)} :=
by simp [sec_exp.run, bind_assoc]

lemma advantage_eq_sum : (parallelization_exp adv).advantage =
  (∑ x₁ x₂ x₃, ⁅= (x₂ -ᵥ x₁) +ᵥ x₃ | adv.run (x₁, x₂, x₃)⁆) / (fintype.card X) ^ 3 :=
have ∀ x₁ x₂ x₃ x₄ : X, x₂ -ᵥ x₁ = x₄ -ᵥ x₃ ↔ x₄ = (x₂ -ᵥ x₁) +ᵥ x₃,
  from λ x₁ x₂ x₃ x₄, eq_comm.trans (eq_vadd_iff_vsub_eq _ _ _).symm,
by simp only [this, sec_exp.advantage, set.preimage, set.mem_def, div_eq_mul_inv, finset.sum_mul,
  mul_assoc, ← pow_three, ← ennreal.inv_pow, run_experiment_eq, is_valid_eq,
  prob_event_uniform_select_fintype_bind_eq_sum, prob_event_bind_return,
  set.set_of_eq_eq_singleton, function.comp, prob_event_eq_eq_prob_output']

end parallelization_exp

/-- Takes in a set of four base points in `X`, attempting to decide if the fourth point
is the correct parallelization of the first three points. -/
def dec_parallelization_adv (G X : Type) :=
sec_adv unif_spec (X × X × X × X) bool

/-- Analogue of the Decisional Diffie-Hellman problem. -/
noncomputable def dec_parallelization_exp (adv : dec_parallelization_adv G X) :
  sec_exp unif_spec bool bool :=
{ inp_gen := $ᵗ bool,
  main := λ b, do
    { x₀ ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G, g₃ ←$ᵗ G,
      x₁ ← return (g₁ +ᵥ x₀), x₂ ← return (g₂ +ᵥ x₀),
      x₃ ← return (if b then g₂ +ᵥ (g₁ +ᵥ x₀) else g₃ +ᵥ x₀),
      adv.run (x₀, x₁, x₂, x₃) },
  is_valid := λ b b', b = b',
  .. base_oracle_algorithm }

namespace decisional_parallelization_exp

variables (adv : dec_parallelization_adv G X)

@[simp] lemma inp_gen_eq : (dec_parallelization_exp adv).inp_gen = $ᵗ bool := rfl

@[simp] lemma main_eq : (dec_parallelization_exp adv).main = λ b, do
  { x₀ ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G, g₃ ←$ᵗ G,
    adv.run (x₀, g₁ +ᵥ x₀, g₂ +ᵥ x₀, if b then g₂ +ᵥ (g₁ +ᵥ x₀) else g₃ +ᵥ x₀) } := rfl

@[simp] lemma is_valid_eq : (dec_parallelization_exp adv).is_valid = eq := rfl

@[simp] lemma to_oracle_algorithm_eq : (dec_parallelization_exp adv).to_oracle_algorithm =
  base_oracle_algorithm := rfl

@[simp] lemma run_eq : (dec_parallelization_exp adv).run = do
  { b ←$ᵗ bool, x₀ ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G, g₃ ←$ᵗ G,
    b' ← adv.run (x₀, g₁ +ᵥ x₀, g₂ +ᵥ x₀, if b then g₂ +ᵥ (g₁ +ᵥ x₀) else g₃ +ᵥ x₀),
    return (b, b') } := by simp [sec_exp.run, bind_assoc]

lemma advantage_eq_add : (dec_parallelization_exp adv).advantage =
  (⁅= tt | do {x ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G,
    adv.run (x, g₁ +ᵥ x, g₂ +ᵥ x, g₂ +ᵥ (g₁ +ᵥ x))}⁆ +
  ⁅= ff | do {x ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G, g₃ ←$ᵗ G,
    adv.run (x, g₁ +ᵥ x, g₂ +ᵥ x, g₃ +ᵥ x)}⁆) / 2 :=
begin
  simp_rw [sec_exp.advantage, run_eq, prob_event_uniform_select_bool_bind],
  congr' 2,
  { simp_rw [← bind_assoc, prob_event_bind_return, is_valid_eq, coe_sort_tt, if_true,
      function.comp, prob_event_eq_eq_prob_output],
    rw_dist_equiv [bind_const_dist_equiv] },
  { simp_rw [← bind_assoc, prob_event_bind_return, is_valid_eq, coe_sort_ff, if_false,
      function.comp, prob_event_eq_eq_prob_output] }
end

lemma advantage_eq_sum : (dec_parallelization_exp adv).advantage =
  (∑ x₀, ∑ g₁ g₂ g₃ : G, (⁅= tt | adv.run (x₀, g₁ +ᵥ x₀, g₂ +ᵥ x₀, g₂ +ᵥ (g₁ +ᵥ x₀))⁆ +
    ⁅= ff | adv.run (x₀, g₁ +ᵥ x₀, g₂ +ᵥ x₀, g₃ +ᵥ x₀)⁆)) / (fintype.card X) ^ 4 / 2 :=
by simp_rw [sec_exp.advantage, run_eq, prob_event_uniform_select_bool_bind,
  prob_event_uniform_select_fintype_bind_eq_sum, card_eq_card, div_eq_mul_inv, ← finset.sum_mul,
  ← add_mul, mul_assoc, is_valid_eq, prob_event_bind_return, coe_sort_tt, coe_sort_ff, if_true, if_false,
  finset.sum_add_distrib, ennreal.inv_pow, pow_succ, pow_zero, mul_one, mul_assoc,
  function.comp, prob_event_eq_eq_prob_output]

end decisional_parallelization_exp

end algorithmic_homogenous_space

open algorithmic_homogenous_space

/-- A `hard_homogenous_space` is an indexed set of `algorithmic_homogenous_space` such that both
vectorization and parallelization become hard as the index becomes large. -/
class hard_homogenous_space (G X : ℕ → Type) [∀ sp, add_comm_group (G sp)]
  [∀ sp, algorithmic_homogenous_space (G sp) (X sp)] :=
(vectorization_hard : ∀ (adversary : Π sp, vectorization_adv (G sp) (X sp)),
  negligable (λ sp, (vectorization_exp (adversary sp)).advantage))
(parallelization_hard : ∀ (adversary : Π (sp : ℕ), parallelization_adv (G sp) (X sp)),
  negligable (λ sp, (parallelization_exp (adversary sp)).advantage))
(dec_parallelization_hard : ∀ (adversary : Π (sp : ℕ), dec_parallelization_adv (G sp) (X sp)),
  negligable (λ sp, (dec_parallelization_exp (adversary sp)).advantage))

namespace hard_homogenous_space


end hard_homogenous_space