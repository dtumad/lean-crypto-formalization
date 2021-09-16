import computational_monads.dist_sem
import computational_complexity.complexity_class
import computational_complexity.negligable

import group_theory.group_action

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space.

`principal_action_class` is a free, transitive group action of `G` on a set `X`.
`algorithmic_homogeneous_space` further requires the group action and group operations are efficiently computable.
`hard_homogeneous_space` further requires vectorization and parallelization are hard.
-/

section action_classes

/-- Mixin typeclass for free actions, where the action of group elements is injective -/
class free_action_class (G X : Type*) [add_monoid G] [add_action G X] : Prop :=
(free (x : X) : function.injective (λ g, g +ᵥ x : G → X))

/-- Mixin typeclass for transitive actions, where the action of group elements is surjective -/
class transitive_action_class (G X : Type*) [add_monoid G] [add_action G X] : Prop :=
(trans (x : X) : function.surjective (λ g, g +ᵥ x : G → X))

/-- Mixin typeclass for actions that are both free and transitive -/
class principal_action_class (G X : Type*) [add_monoid G] [add_action G X]
  extends free_action_class G X, transitive_action_class G X : Prop

variables {G X : Type*} [add_monoid G] [add_action G X]

lemma free_action_class_iff :
  free_action_class G X ↔ ∀ (x : X) (g g' : G), g +ᵥ x = g' +ᵥ x → g = g' :=
begin
  split,
  { introsI h x,
    exact free_action_class.free x },
  { exact λ h, { free := h } }
end

lemma free_action_class.vadd_eq_iff [free_action_class G X] 
  (x : X) (g g' : G) : g +ᵥ x = g' +ᵥ x ↔ g = g' :=
⟨λ hx, free_action_class.free x hx, λ h, congr_arg _ h⟩

lemma free_action_class.eq_of_vadd_eq [free_action_class G X] 
  (x : X) {g g' : G} (h : g +ᵥ x = g' +ᵥ x) : g = g' :=
(free_action_class.vadd_eq_iff x g g').mp h

lemma transitive_action_class_iff :
  transitive_action_class G X ↔ ∀ (x y : X), ∃ (g : G), g +ᵥ x = y :=
begin
  split,
  { introsI h x,
    exact transitive_action_class.trans x },
  { exact λ h, { trans := h } }
end

lemma transitive_action_class.exists_vadd_eq [transitive_action_class G X]
  (x y : X) : ∃ (g : G), g +ᵥ x = y :=
transitive_action_class.trans x y

lemma principal_action_class_iff_bijective :
  principal_action_class G X ↔ ∀ x, function.bijective (λ g, g +ᵥ x : G → X) :=
begin
  split,
  { introsI h x,
    refine ⟨free_action_class.free x, transitive_action_class.trans x⟩ },
  { intro h,
    haveI : free_action_class G X := { free := λ x, (h x).1 },
    haveI : transitive_action_class G X := { trans := λ x, (h x).2 },
    exact {} }
end

theorem principal_action_class.vectorization_unique [principal_action_class G X] 
  (x y : X) : ∃! (g : G), g +ᵥ x = y :=
exists_unique_of_exists_of_unique (transitive_action_class.exists_vadd_eq x y)
  (λ g g' hg hg', free_action_class.eq_of_vadd_eq x (hg.trans hg'.symm))

variables (G X)

lemma free_action_class.card_le_card [free_action_class G X]
  [fintype G] [fintype X] [inhabited X] :
  fintype.card G ≤ fintype.card X :=
fintype.card_le_of_injective (λ g, g +ᵥ (arbitrary X)) (free_action_class.free $ arbitrary X)

lemma transitive_action_class.card_le_card [transitive_action_class G X]
  [fintype G] [fintype X] [inhabited X] :
  fintype.card X ≤ fintype.card G :=
fintype.card_le_of_surjective (λ g, g +ᵥ (arbitrary X)) (transitive_action_class.trans $ arbitrary X)

theorem principal_action_class.fintype_card_eq [principal_action_class G X]
  [fintype G] [fintype X] [inhabited X] :
  fintype.card G = fintype.card X :=
le_antisymm (free_action_class.card_le_card G X) (transitive_action_class.card_le_card G X)

noncomputable def principal_action_class.equiv [principal_action_class G X]
  [fintype G] [fintype X] [inhabited X] : G ≃ X :=
fintype.equiv_of_card_eq (principal_action_class.fintype_card_eq G X)

variables {G X}

section vectorization

variable (G)

/-- The vectorization of `x` and `y` is the unique element of `g` sending `x` to `y` under the action.
In the case where the homogeneous space is the Diffie-Hellman action this is the discrete log -/
def vectorization [principal_action_class G X] [fintype G] [decidable_eq X] (x y : X) : G :=
fintype.choose (λ g, g +ᵥ x = y) (principal_action_class.vectorization_unique x y)

variables [principal_action_class G X]
  [fintype G] [decidable_eq X]

@[simp]
lemma vectorization_apply (x y : X) :
  (vectorization G x y) +ᵥ x = y :=
fintype.choose_spec (λ g, g +ᵥ x = y) (principal_action_class.vectorization_unique x y)

variable {G}

@[simp]
lemma vectorization_vadd (x : X) (g : G) :
  vectorization G x (g +ᵥ x) = g :=
begin
  refine free_action_class.eq_of_vadd_eq x _,
  simp,
end

@[simp]
lemma eq_vectorization_iff (g : G) (x y : X) :
  g = vectorization G x y ↔ y = g +ᵥ x :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [h, vectorization_apply] },
  { rw [h, vectorization_vadd] }
end

lemma vadd_eq_vadd_iff_left (g g' : G) (x y : X) :
  g +ᵥ x = g' +ᵥ y ↔ g = g' + vectorization G x y :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← vectorization_apply G x y at h,
    rw vadd_vadd at h,
    refine free_action_class.eq_of_vadd_eq x h },
  { rw [h, ← vadd_vadd, vectorization_apply] }
end

lemma vectorization_swap (G : Type) {X : Type} [add_group G] [add_action G X]
  [principal_action_class G X] [fintype G] [decidable_eq X]
  (x y : X) : (vectorization G x y) = - (vectorization G y x) :=
begin
  refine free_action_class.eq_of_vadd_eq x _,
  simp [eq_neg_vadd_iff],
end

end vectorization

end action_classes


section computational_advantages

variables {G X : Type} [fintype G] [fintype X] 
  [inhabited G] [inhabited X] 
  [decidable_eq X] [decidable_eq G]
variables [add_monoid G] [add_action G X] [principal_action_class G X]

/-- Analogue of Discrete-logarithm asumption game -/
@[derive comp.is_well_formed]
def vectorization_experiment (A : X × X → comp G)
  [∀ x y, (A (x, y)).is_well_formed] : comp bool :=
do x₁ ← comp.rnd X,
  x₂ ← comp.rnd X,
  g ← A (x₁, x₂),
  return (g = vectorization G x₁ x₂)

/-- Vectorization advantage of an adversary in the vectorization experiment. -/
noncomputable def vectorization_advantage (adversary : X × X → comp G) 
  [∀ x y, (adversary (x, y)).is_well_formed] : ℝ :=
(comp.Pr (vectorization_experiment adversary))
- (comp.Pr (vectorization_experiment (λ (_ : X × X), comp.rnd G)))

variable (G)

/-- Analogue of the decisional Diffie-Helman experiment -/
@[derive comp.is_well_formed]
def parallelization_experiment (A : X × X × X → comp X)
  [∀ x y z, (A (x, y, z)).is_well_formed] : comp bool :=
do x₁ ← (comp.rnd X),
  x₂ ← (comp.rnd X),
  x₃ ← (comp.rnd X),
  x₄ ← (A (x₁, x₂, x₃) : comp X),
  return ((vectorization G x₂ x₁) = (vectorization G x₄ x₃))

/-- Parallelization advantage of an adversary in parallelization experiment -/
noncomputable def parallelization_advantage (adversary : X × X × X → comp X) 
  [∀ x y z, (adversary (x, y, z)).is_well_formed] : ℝ :=
(comp.Pr (parallelization_experiment G adversary))
- (comp.Pr (parallelization_experiment G (λ (_ : X × X × X), comp.rnd X)))

end computational_advantages


section hard_homogeneous_space
variable [function_cost_model ℚ]
variables  [comp_cost_model ℚ]
variables (G X : ℕ → Type) 
  [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, inhabited (G n)] [∀ n, inhabited (X n)]
  [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
  [∀ n, add_comm_group (G n)] [∀ n, add_action (G n) (X n)]
  [∀ n, principal_action_class (G n) (X n)]

/-- A homogenous space is defined by a parameterized collection of homogenous spaces (`principal_action_class`).
  `G` and `X` together define a generation algorithm for homogenous spaces from a security parameter,
    and we want the following operations to have polynomial-growth time in the security parameter.

  Note that we model `G n` and `X n` as having some *fixed* internal representation,
    so this definition doesn't include functions for converting to and from representative bit-strings.
  TODO: clean up the many typeclass dependencies -/
class algorithmic_homogeneous_space :=
(polynomial_complexity_add : 
  complexity_class.polynomial_complexity (λ sp, (λ x, x.1 + x.2 : G sp × G sp → G sp)))
(polynomial_complexity_inv :
  complexity_class.polynomial_complexity (λ sp, (λ x, -x : G sp → G sp)))
(polynomial_complexity_vadd : 
  complexity_class.polynomial_complexity (λ n, (λ x, x.1 +ᵥ x.2 : G n × X n → X n)))
(polynomial_complexity_eq_G : 
  complexity_class.polynomial_complexity (λ n, (λ x, x.1 = x.2 : G n × G n → Prop)))
(polynomial_complexity_eq_X : 
  complexity_class.polynomial_complexity (λ n, (λ x, x.1 = x.2 : X n × X n → Prop)))
(polynomial_complexity_rnd_G : 
  complexity_class.polynomial_complexity (λ n, (λ x, comp.rnd (G n) : unit → comp (G n))))

section algorithmic_homogeneous_space

-- -- TODO: derive rnd X efficient by choosing a generator and using G_rnd_efficient
lemma polynomial_complexity_rnd_X [h : algorithmic_homogeneous_space G X] 
  [pairing_cost_extension ℚ] : 
  complexity_class.polynomial_complexity (λ n, (λ x, comp.rnd (X n) : unit → comp (X n))) :=
begin
  have : complexity_class.polynomial_complexity
    (λ n, (λ x, do {
      g ← comp.rnd (G n),
      return (g +ᵥ (default _))
    } : unit → comp (X n))),
  { refine complexity_class.polynomial_complexity_comp_bind _ _,
    refine algorithmic_homogeneous_space.polynomial_complexity_rnd_G X,
    refine complexity_class.polynomial_complexity_comp_unit_prod _ _,
    refine complexity_class.polynomial_complexity_comp_ret_of_polynomial_complexity _,
    exact complexity_class.polynomial_complexity_comp_ext 
      (complexity_class.polynomial_complexity_of_has_cost_zero (λ n, (λ g, (g, default _) : G n → G n × X n))) 
      (h.polynomial_complexity_vadd) (by simp) },
      
  refine complexity_class.polynomial_complexity_comp_ext' (λ n _, _) this,
  refine pmf.ext (λ x, _),
  simp only [mul_boole, comp.monad_to_has_bind_bind, comp.eval_distribution_rnd, pmf.const_apply, pmf.pure_apply,
    comp.eval_distribution_bind, pmf.bind_apply, comp.return_eq, comp.eval_distribution_ret],
  refine trans (tsum_congr (λ g, _)) (tsum_ite_eq (vectorization (G n) (default _) x) _),
  simp_rw [eq_vectorization_iff],
  refine congr (congr (by congr) _) rfl,
  simpa using principal_action_class.fintype_card_eq (G n) (X n),
end

end algorithmic_homogeneous_space

structure vectorization_adversary (G X : ℕ → Type) :=
(A : Π sp, X sp × X sp → comp (G sp))
(is_well_formed : ∀ sp x, (A sp x).is_well_formed)
(polynomial_complexity : complexity_class.polynomial_complexity A)

instance vectorization_advesary.is_well_formed' {G X : ℕ → Type}
  (adv : vectorization_adversary G X) (sp : ℕ) (x : X sp × X sp) :
  (adv.A sp x).is_well_formed :=
adv.is_well_formed sp x

structure parallelization_adversary (X : ℕ → Type) :=
(A : Π sp, X sp × X sp × X sp → comp (X sp))
(is_well_formed : ∀ sp x, (A sp x).is_well_formed)
(polynomial_complexity : complexity_class.polynomial_complexity A)

instance parallelization_adversary.is_well_formed' {X : ℕ → Type}
  (adv : parallelization_adversary X) (sp : ℕ) (x : X sp × X sp × X sp) :
  (adv.A sp x).is_well_formed :=
adv.is_well_formed sp x

/-- Extension of `algorithmic_homogenous_space` with hardness assumptions.
  Vectorization and parallelization correspond to discrete-log and Diffie-Hellman -/
class hard_homogeneous_space extends algorithmic_homogeneous_space G X :=
(vectorization_hard : ∀ (adv : vectorization_adversary G X),
  asymptotics.negligable (λ sp, vectorization_advantage (adv.A sp)))
(parallelization_hard : ∀ (adv : parallelization_adversary X),
  asymptotics.negligable (λ n, parallelization_advantage (G n) (adv.A n)))

end hard_homogeneous_space
