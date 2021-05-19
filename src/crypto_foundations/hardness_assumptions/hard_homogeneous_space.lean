import crypto_foundations.dist_sem
import computational_complexity.complexity_class
import computational_complexity.negligable
import group_theory.group_action

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space in several steps.

`homogenous_space` is a transitive group action of `G` on a set `X` of equal size.
`algorithmic_homogenous_space` further assumes the group action and group operations are efficiently computable.
`hard_homogenous_space` further assumes vectorization and parallelization are hard.
-/

universes u v

section transitive_action

-- TODO: add more theory and move this to mathlib
class transitive_action (G X : Type u) [monoid G] extends mul_action G X :=
(exists_smul_eq : ∀ (x y : X), ∃ (g : G), g • x = y)

end transitive_action

section homogeneous_space

/-- A `homogenous_space G X` extends a transitive action with a proof that `G` and `X` have the same size -/
class homogeneous_space (G X : Type u) [fintype G] [fintype X] [decidable_eq X]
  extends comm_group G, transitive_action G X :=
(size_eq : fintype.card G = fintype.card X)

variables {G X : Type u} [fintype G] [fintype X] [decidable_eq X]

instance homogeneous_space.inhabited [homogeneous_space G X] : inhabited G := ⟨1⟩

lemma homogeneous_space.smul_bijective [homogeneous_space G X] (x : X) :
  function.bijective (λ g, g • x : G → X) :=
(fintype.bijective_iff_surjective_and_card _).mpr
  ⟨transitive_action.exists_smul_eq x, homogeneous_space.size_eq⟩

@[simp] theorem different_action [homogeneous_space G X] (g1 g2 : G) (x : X) :
  g1 • x = g2 • x ↔ g1 = g2 :=
⟨λ h, (homogeneous_space.smul_bijective x).1 h, λ h, congr_arg _ h⟩

theorem transitive_action_unique [homogeneous_space G X] (x y : X) :
  ∃! (g : G), g • x = y :=
exists_unique_of_exists_of_unique (transitive_action.exists_smul_eq x y)
  $ λ g1 g2 hg1 hg2, (different_action g1 g2 x).mp (trans hg1 hg2.symm)

@[simp] lemma no_fixed_points [homogeneous_space G X] (g : G) (x : X) :
  g • x = x ↔ g = 1 :=
⟨λ h, (different_action g 1 x).mp (trans h (one_smul G x).symm), λ hg, hg.symm ▸ (one_smul G x)⟩

/-- The vectorization of `x` and `y` is the unique element of `g` sending `x` to `y` under the action.
In the case where the homogenous space is the Diffie-Hellman action this is the discrete log -/
def vectorization [homogeneous_space G X] (x y : X) : G :=
fintype.choose (λ g, g • x = y) (transitive_action_unique x y)

lemma vectorization_smul_eq [homogeneous_space G X] (x y : X) :
  (vectorization x y : G) • x = y :=
fintype.choose_spec (λ g, g • x = y) _

end homogeneous_space

section computational_advantages

variables {G X : Type} [fintype G] [fintype X] [inhabited X] 
  [decidable_eq X] [decidable_eq G] [homogeneous_space G X]

local notation `δ` := vectorization

/-- Analogue of Discrete-logarithm asumption game -/
def vectorization_experiment (adversary : X × X → comp G) : comp bool :=
(comp.bind (comp.rnd X) (λ x1, 
  comp.bind (comp.rnd X) (λ x2,
  comp.bind (adversary (x1, x2)) (λ g,
  comp.ret (g = vectorization x1 x2)))))

instance well_formed_comp_vectorization_experiment {f : X × X → comp G} 
  [∀ x y, (f (x, y)).is_well_formed] : (vectorization_experiment f).is_well_formed :=
by simpa [vectorization_experiment]

/-- Cectorization advantage of an adversary in the vectorization experiment. -/
noncomputable def vectorization_advantage (adversary : X × X → comp G) 
  [∀ x y, (adversary (x, y)).is_well_formed] : ℝ :=
(comp.Pr (vectorization_experiment adversary))
- (comp.Pr (vectorization_experiment (λ (_ : X × X), comp.rnd G)))

/-- Analogue of the Diffie-Helman assumption game -/
def parallelization_experiment (G : Type) [fintype G] [decidable_eq G]
  [homogeneous_space G X] (adversary : X × X × X → comp X) : comp bool :=
(comp.bind (comp.rnd X) (λ x1,
  comp.bind (comp.rnd X) (λ x2,
  comp.bind (comp.rnd X) (λ x3,
  comp.bind (adversary (x1, x2, x3) : comp X) (λ x4,
  comp.ret ((δ x2 x1 : G) = (δ x4 x3 : G)))))))

instance well_formed_comp_parallelization_experiment {f : X × X × X → comp X} 
  [∀ x y z, (f (x, y, z)).is_well_formed] : 
  (parallelization_experiment G f).is_well_formed :=
by simpa [parallelization_experiment]

/-- Parallelization advantage of an adversary in parallelization experiment -/
noncomputable def parallelization_advantage (G : Type) [fintype G] [decidable_eq G]
  [homogeneous_space G X] (adversary : X × X × X → comp X) 
  [∀ x y z, (adversary (x, y, z)).is_well_formed] : ℝ :=
(comp.Pr (parallelization_experiment G adversary))
- (comp.Pr (parallelization_experiment G (λ (_ : X × X × X), comp.rnd X)))

end computational_advantages

section hard_homogeneous_space

class algorithmic_homogeneous_space (G X : ℕ → Type) 
  [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
  [∀ n, homogeneous_space (G n) (X n)] :=
(mul_efficient : log_poly_time_cost (λ n, (λ x, x.1 * x.2 : G n × G n → G n)))
(inv_efficient : log_poly_time_cost (λ n, (λ x, x⁻¹ : G n → G n)))
(smul_efficient : log_poly_time_cost (λ n, (λ x, x.1 • x.2 : G n × X n → X n)))
(G_eq_efficient : log_poly_time_cost (λ n, (λ x, x.1 = x.2 : G n × G n → Prop)))
(X_eq_efficient : log_poly_time_cost (λ n, (λ x, x.1 = x.2 : X n × X n → Prop)))
(G_rnd_efficient : log_poly_time_comp (λ n, comp.rnd (G n)))

variables (G X : ℕ → Type) [∀ n, fintype (G n)] [∀ n, fintype (X n)] 
  [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
  [∀ n, homogeneous_space (G n) (X n)] [∀ n, decidable_eq (G n)]
  [algorithmic_homogeneous_space G X]

lemma mul_right_efficient [H : algorithmic_homogeneous_space G X] (g : Π n, G n) :
  log_poly_time_cost (λ n, λ (x : G n), (g n) * x) :=
let ⟨f, hf, hf'⟩ := H.mul_efficient in
  ⟨f, hf, λ n, has_cost.has_cost_of_uncurry' (g n) (hf' n)⟩

lemma mul_left_efficient [algorithmic_homogeneous_space G X] (g : Π n, G n) :
  log_poly_time_cost (λ n, λ (x : G n), x * (g n)) :=
log_poly_time_cost_ext (mul_right_efficient G X g) (λ n x, mul_comm (g n) x)
 
class hard_homogeneous_space (G X : ℕ → Type) [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, inhabited (X n)] [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)] 
  [∀ n, homogeneous_space (G n) (X n)]
  extends algorithmic_homogeneous_space G X :=
(vectorization_hard : ∀ (f : Π n, X n × X n → comp (G n))
  [∀ n x y, (f n (x, y)).is_well_formed] (h : poly_time_cost f),
  negligable (λ n, vectorization_advantage (f n)))
(parallelization_hard : ∀ (f : Π n, X n × X n × X n → comp (X n))
  [∀ n x y z, (f n (x, y, z)).is_well_formed] (h : poly_time_cost f),
  negligable (λ n, parallelization_advantage (G n) (f n)))

end hard_homogeneous_space
