import crypto_foundations.comp
import computational_complexity.cost_model
import group_theory.group_action

universes u v

section transitive_action

-- TODO: add more theory and move this to mathlib
class transitive_action (G X : Type u) [monoid G] extends mul_action G X :=
(exists_smul_eq : ∀ (x y : X), ∃ (g : G), g • x = y)

end transitive_action

section homogeneous_space

class homogenous_space (G X : Type u) [fintype G] [fintype X] [decidable_eq X]
  extends comm_group G, transitive_action G X :=
(size_eq : fintype.card G = fintype.card X)

variables {G X : Type u} [fintype G] [fintype X] [decidable_eq X]

instance homogenous_space.inhabited [homogenous_space G X] : inhabited G := ⟨1⟩

lemma homogenous_space.smul_bijective [homogenous_space G X] (x : X) :
  function.bijective (λ g, g • x : G → X) :=
(fintype.bijective_iff_surjective_and_card _).mpr
  ⟨transitive_action.exists_smul_eq x, homogenous_space.size_eq⟩

@[simp] theorem different_action [homogenous_space G X] (g1 g2 : G) (x : X) :
  g1 • x = g2 • x ↔ g1 = g2 :=
⟨λ h, (homogenous_space.smul_bijective x).1 h, λ h, congr_arg _ h⟩

theorem transitive_action_unique [homogenous_space G X] (x y : X) :
  ∃! (g : G), g • x = y :=
exists_unique_of_exists_of_unique (transitive_action.exists_smul_eq x y)
  $ λ g1 g2 hg1 hg2, (different_action g1 g2 x).mp (trans hg1 hg2.symm)

def parallelization [homogenous_space G X] (x y : X) : G :=
fintype.choose _ (transitive_action_unique x y)

local notation `δ` := parallelization

lemma parallelization_smul_eq [homogenous_space G X] (x y : X) :
  (δ x y : G) • x = y :=
fintype.choose_spec (λ g, g • x = y) _

@[simp] lemma no_fixed_points [homogenous_space G X] (g : G) (x : X) :
  g • x = x ↔ g = 1 :=
⟨λ h, (different_action g 1 x).mp (trans h (one_smul G x).symm), λ hg, hg.symm ▸ (one_smul G x)⟩

end homogeneous_space

section hard_homogeneous_space

class algorithmic_homogeneous_space (G X : ℕ → Type) 
  [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
  [∀ n, homogenous_space (G n) (X n)] :=
(mul_efficient : log_poly_time_cost (λ n, (λ x, x.1 * x.2 : G n × G n → G n)))
(inv_efficient : log_poly_time_cost (λ n, (λ x, x⁻¹ : G n → G n)))
(smul_efficient : log_poly_time_cost (λ n, (λ x, x.1 • x.2 : G n × X n → X n)))
(G_eq_efficient : log_poly_time_cost (λ n, (λ x, x.1 = x.2 : G n × G n → Prop)))
(X_eq_efficient : log_poly_time_cost (λ n, (λ x, x.1 = x.2 : X n × X n → Prop)))
(G_rnd_efficient : log_poly_time_comp (λ n, comp.rnd (G n)))

variables (G X : ℕ → Type) [∀ n, fintype (G n)] [∀ n, fintype (X n)] 
  [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
  [∀ n, homogenous_space (G n) (X n)] [∀ n, decidable_eq (G n)]
  [algorithmic_homogeneous_space G X]

lemma mul_right_efficient [H : algorithmic_homogeneous_space G X] (g : Π n, G n) :
  log_poly_time_cost (λ n, λ (x : G n), (g n) * x) :=
let ⟨f, hf, hf'⟩ := H.mul_efficient in
  ⟨f, hf, λ n, has_cost.has_cost_of_uncurry' (g n) (hf' n)⟩

lemma mul_left_efficient [algorithmic_homogeneous_space G X] (g : Π n, G n) :
  log_poly_time_cost (λ n, λ (x : G n), x * (g n)) :=
log_poly_time_cost_ext (mul_right_efficient G X g) (λ n x, mul_comm (g n) x)

-- def vectorization_solution (G X : ℕ → Type)

-- class hard_homogeneous_space (G X : ℕ → Type) [∀ n, fintype (G n)] [∀ n, fintype (X n)]
--   [∀ n, decidable_eq (G n)]  [∀ n, decidable_eq (X n)] [∀ n, homogenous_space (G n) (X n)]
--   extends algorithmic_homogeneous_space G X :=
-- (vectorization_hard : ∀ (f : Π n, X n × X n → G n)
--   (hf : ∀ n x, (f n x) = parallelization x.1 x.2), ¬ poly_time_cost f)
-- (parellelization_hard : ∀ (f : Π n, X n × X n × X n → X n)
--   (hf : ∀ n x, parallelization (f n x) x.1 = parallelization x.2.1 x.2.2), ¬ poly_time_cost f)

end hard_homogeneous_space
