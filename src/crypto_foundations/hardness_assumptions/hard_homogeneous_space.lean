import crypto_foundations.dist_sem
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

section vectorization

/-- The vectorization of `x` and `y` is the unique element of `g` sending `x` to `y` under the action.
In the case where the homogeneous space is the Diffie-Hellman action this is the discrete log -/
def vectorization [principal_action_class G X] [fintype G] [decidable_eq X] (x y : X) : G :=
fintype.choose (λ g, g +ᵥ x = y) (principal_action_class.vectorization_unique x y)

variables [principal_action_class G X]
  [fintype G] [decidable_eq X]

variable (G)

@[simp]
lemma vectorization_apply (x y : X) :
  (vectorization x y : G) +ᵥ x = y :=
fintype.choose_spec (λ g, g +ᵥ x = y) (principal_action_class.vectorization_unique x y)

variable {G}

@[simp]
lemma vectorization_vadd (x : X) (g : G) :
  vectorization x (g +ᵥ x) = g :=
begin
  refine free_action_class.eq_of_vadd_eq x _,
  simp,
end

lemma principal_action_class.vadd_eq_iff_left (g g' : G) (x y : X) :
  g +ᵥ x = g' +ᵥ y ↔ g = g' + (vectorization x y) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← vectorization_apply G x y at h,
    rw vadd_vadd at h,
    refine free_action_class.eq_of_vadd_eq x h },
  { rw [h, ← vadd_vadd, vectorization_apply] }
end

lemma vectorization_swap (G : Type) {X : Type} [add_group G] [add_action G X]
  [principal_action_class G X] [fintype G] [decidable_eq X]
  (x y : X) : (vectorization x y : G) = - (vectorization y x : G) :=
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

local notation `δ` := vectorization

/-- Analogue of Discrete-logarithm asumption game -/
def vectorization_experiment (adversary : X × X → comp G) : comp bool :=
(comp.bind (comp.rnd X) (λ x1, 
  comp.bind (comp.rnd X) (λ x2,
  comp.bind (adversary (x1, x2)) (λ g,
  comp.ret (g = δ x1 x2)))))

instance vectorization_experiment.is_well_formed {f : X × X → comp G} 
  [∀ x y, (f (x, y)).is_well_formed] : (vectorization_experiment f).is_well_formed :=
by simp [vectorization_experiment]

/-- Vectorization advantage of an adversary in the vectorization experiment. -/
noncomputable def vectorization_advantage (adversary : X × X → comp G) 
  [∀ x y, (adversary (x, y)).is_well_formed] : ℝ :=
(comp.Pr (vectorization_experiment adversary))
- (comp.Pr (vectorization_experiment (λ (_ : X × X), comp.rnd G)))

variable (G)

/-- Analogue of the decisional Diffie-Helman experiment -/
def parallelization_experiment (adversary : X × X × X → comp X) : comp bool :=
(comp.bind (comp.rnd X) (λ x1,
  comp.bind (comp.rnd X) (λ x2,
  comp.bind (comp.rnd X) (λ x3,
  comp.bind (adversary (x1, x2, x3) : comp X) (λ x4,
  comp.ret ((δ x2 x1 : G) = (δ x4 x3 : G)))))))

instance parallelization_experiment.is_well_formed {f : X × X × X → comp X} 
  [∀ x y z, (f (x, y, z)).is_well_formed] : 
  (parallelization_experiment G f).is_well_formed :=
by simp [parallelization_experiment]

/-- Parallelization advantage of an adversary in parallelization experiment -/
noncomputable def parallelization_advantage (adversary : X × X × X → comp X) 
  [∀ x y z, (adversary (x, y, z)).is_well_formed] : ℝ :=
(comp.Pr (parallelization_experiment G adversary))
- (comp.Pr (parallelization_experiment G (λ (_ : X × X × X), comp.rnd X)))

end computational_advantages


section hard_homogeneous_space

/-- A homogenous space is defined by a parameterized collection of homogenous spaces (`principal_action_class`).
  `G` and `X` together define a generation algorithm for homogenous spaces from a security parameter,
    and we want the following operations to have polynomial-growth time in the security parameter.

  Note that we model `G n` and `X n` as having some *fixed* internal representation,
    so this definition doesn't include functions for converting to and from representative bit-strings.
  TODO: clean up the massive typeclass dependencies -/
class algorithmic_homogeneous_space (G X : ℕ → Type) 
  [∀ n, inhabited (G n)] [∀ n, inhabited (X n)]
  [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
  [∀ n, add_comm_group (G n)] [∀ n, add_action (G n) (X n)]
  [∀ n, principal_action_class (G n) (X n)] :=
-- TODO: see if they should use fun₂ version instead of currying
(add_efficient : complexity_class.poly_time_fun₁
  (λ sp, (λ x, x.1 + x.2 : G sp × G sp → G sp)))
(inv_efficient : complexity_class.poly_time_fun₁ 
  (λ sp, (λ x, -x : G sp → G sp)))
(vadd_efficient : complexity_class.poly_time_fun₁ 
  (λ n, (λ x, x.1 +ᵥ x.2 : G n × X n → X n)))
(G_eq_efficient : complexity_class.poly_time_fun₁ 
  (λ n, (λ x, x.1 = x.2 : G n × G n → Prop)))
(X_eq_efficient : complexity_class.poly_time_fun₁ 
  (λ n, (λ x, x.1 = x.2 : X n × X n → Prop)))
(G_rnd_efficient : complexity_class.poly_time_comp₀ 
  (λ n, comp.rnd (G n)))
-- TODO: This is needed right? to actually construct more complicated functions
(G_copy_efficient : complexity_class.poly_time_fun₁ 
  (λ n, (λ g, (g, g) : G n → G n × G n)))
(X_copy_efficient : complexity_class.poly_time_fun₁ 
  (λ n, (λ x, (x, x) : X n → X n × X n)))

-- TODO: derive rnd X efficient by choosing a generator and using G_rnd_efficient

variables (G X : ℕ → Type) 
  [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, inhabited (G n)] [∀ n, inhabited (X n)]
  [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
  [∀ n, add_comm_group (G n)] [∀ n, add_action (G n) (X n)]
  [∀ n, principal_action_class (G n) (X n)]

lemma add_right_efficient [H : algorithmic_homogeneous_space G X] (g : Π n, G n) :
  complexity_class.poly_time_fun₁ (λ n, λ (x : G n), (g n) + x) :=
let ⟨f, hf, hf'⟩ := H.add_efficient in
  ⟨f, hf, λ n, has_cost.has_cost_of_uncurry' (g n) (hf' n)⟩

-- lemma mul_left_efficient [algorithmic_homogeneous_space G X] (g : Π n, G n) :
--   complexity_class.poly_time_fun₁ (λ n, λ (x : G n), x * (g n)) :=
-- poly_time_cost_ext (mul_right_efficient G X g) (λ n x, mul_comm (g n) x)

/-- Extension of `algorithmic_homogenous_space` with hardness assumptions.
  Vectorization and parallelization correspond to discrete-log and Diffie-Hellman -/
class hard_homogeneous_space extends algorithmic_homogeneous_space G X :=
(vectorization_hard : ∀ (A : Π sp, X sp × X sp → comp (G sp)) 
  [∀ sp x y, (A sp (x, y)).is_well_formed] 
  (h : complexity_class.poly_time_comp₁ A),
  asymptotics.negligable (λ sp, vectorization_advantage (A sp)))
(parallelization_hard : ∀ (A : Π sp, X sp × X sp × X sp → comp (X sp))
  [∀ sp x y z, (A sp (x, y, z)).is_well_formed]
  (h : complexity_class.poly_time_comp₁ A),
  asymptotics.negligable (λ n, parallelization_advantage (G n) (A n)))

end hard_homogeneous_space
