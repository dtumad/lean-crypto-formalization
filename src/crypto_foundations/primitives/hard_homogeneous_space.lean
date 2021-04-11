import crypto_foundations.comp
import computational_complexity.cost_model
import group_theory.group_action

universes u v

section transitive_action

-- TODO: add more theory and move this to mathlib
class transitive_action (G X : Type u) [monoid G] extends mul_action G X :=
(transitive : ∀ (x y : X), ∃ (g : G), g • x = y)

end transitive_action

section homogeneous_space

class homogenous_space (G X : Type u) [fintype G] [fintype X]
  extends comm_group G, transitive_action G X :=
(size_eq : fintype.card G = fintype.card X)

variables {G X : Type u} [fintype G] [fintype X]

instance homogenous_space.inhabited [homogenous_space G X] : inhabited G := ⟨1⟩

@[simp] lemma different_action [homogenous_space G X] (g1 g2 : G) (x : X) :
  g1 • x = g2 • x ↔ g1 = g2 :=
begin
  refine ⟨sorry, λ h, congr_arg _ h⟩,
end

@[simp] lemma no_fixed_points [homogenous_space G X] (g : G) (x : X) :
  g • x = x ↔ g = 1 :=
⟨λ h, (different_action g 1 x).mp (trans h (one_smul G x).symm), λ hg, hg.symm ▸ (one_smul G x)⟩

end homogeneous_space

section hard_homogeneous_space

class hard_homogeneous_space (G X : ℕ → Type) [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, homogenous_space (G n) (X n)] [∀ n, decidable_eq (G n)] :=
(mul_efficient : log_poly_time_cost (λ n, (λ x, x.1 * x.2 : G n × G n → G n)))
(inv_efficient : log_poly_time_cost (λ n, (λ x, x⁻¹ : G n → G n)))
(smul_efficient : log_poly_time_cost (λ n, (λ x, x.1 • x.2 : G n × X n → X n)))
(G_eq_efficient : log_poly_time_cost (λ n, (λ x, x.1 = x.2 : G n × G n → Prop)))
(X_eq_efficient : log_poly_time_cost (λ n, (λ x, x.1 = x.2 : X n × X n → Prop)))
(G_rnd_efficient : log_poly_time_comp (λ n, comp.rnd (G n)))
(vectorization : ∀ (f : Π n, X n × X n → G n) (hf : ∀ n x, (f n x) • x.1 = x.2), ¬ poly_time_cost f)

variables (G X : ℕ → Type) [∀ n, fintype (G n)] [∀ n, fintype (X n)]
variables [∀ n, homogenous_space (G n) (X n)] [∀ n, decidable_eq (G n)]

lemma mul_right_efficient [H : hard_homogeneous_space G X] (g : Π n, G n) :
  log_poly_time_cost (λ n, λ (x : G n), (g n) * x) :=
let ⟨f, hf, hf'⟩ := H.mul_efficient in
  ⟨f, hf, λ n, has_cost.has_cost_of_uncurry' (g n) (hf' n)⟩

lemma mul_left_efficient [H : hard_homogeneous_space G X] (g : Π n, G n) :
  log_poly_time_cost (λ n, λ (x : G n), x * (g n)) :=
log_poly_time_cost_ext (mul_right_efficient G X g) (λ n x, mul_comm (g n) x)

end hard_homogeneous_space
