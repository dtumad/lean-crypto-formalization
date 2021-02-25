import comp
import cost_model
import group_theory.group_action

universes u v

section transitive_action

class transitive_action (G X : Type u) [monoid G] extends mul_action G X :=
(trans : ∀ (x y : X), ∃ (g : G), g • x = y)

end transitive_action

section hard_homogeneous_space

-- class hard_homogeneous_space (G X : Type)
--   extends comm_group G, fintype G, transitive_action G X :=
-- (gmul_Comp : G → G → Comp G)
-- (gmul_Comp_semantics : ∀ x y, (gmul_Comp x y).support = {x * y})
-- (gmul_Comp_efficient : ∀ x y, comp_cost @has_cost (gmul_Comp x y) 0)

-- class hard_homogeneous_space (G X : ℕ → Type) 
--   [∀ {n}, comm_group (G n)] [∀ {n}, transitive_action (G n) (X n)] :=
-- (gmul_Comp : ∀ n, G n → G n → Comp (G n))
-- (gmul_Comp_semantics : ∀ n x y, (gmul_Comp n x y).support = {x * y})
-- (gmul_Comp_efficient : poly_growth gmul_Comp)
-- (smul_Comp : ∀ n, G n → X n → Comp (X n))
-- (smul_Comp_semantics : ∀ n g x, (smul_Comp n g x).support = {g • x})

def poly_time_has_cost {A B : ℕ → Type} (c : ∀ (n : ℕ), ((A n) → (B n))) :=
  ∃ (f : ℕ → ℕ), poly_growth f ∧ (∀ n, has_cost (c n) (f n))

class hard_homogenous_space (G X : ℕ → Type)
  [hG : ∀ n, comm_group (G n)] [∀ {n}, transitive_action (G n) (X n)] :=
(G_mul_inefficient : ¬ poly_time_has_cost (λ n, (function.uncurry (hG n).mul : G n × G n → G n)))


example (G X : ℕ → Type) [∀ n, comm_group (G n)] [∀ {n}, transitive_action (G n) (X n)]
  [H : hard_homogenous_space G X] : false :=
begin
  apply H.G_mul_inefficient,
  refine ⟨id, sorry, _⟩,
  {
    simp,
    intro n,
    
  }
end

end hard_homogeneous_space
