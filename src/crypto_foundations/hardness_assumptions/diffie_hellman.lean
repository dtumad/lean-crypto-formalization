import computational_complexity.cost_model
import crypto_foundations.dist_sem

open_locale big_operators

variables (G : Type) [group G] 

-- def diffie_hellman_candidate := G × G × G → comp G

-- def diffie_hellman_experiment (f : diffie_hellman_candidate G) 
--   (hf : ∀ x, comp.well_formed_comp (f x)) : comp bool :=
-- comp.bind

-- def diffie_hellman_advantage (f : diffie_hellman_candidate G) :=
-- comp.Pr

-- def diffie_hellman_solution (f : diffie_hellman_candidate G) := 
-- ∀ (x y : ℕ) (g : G), f (g, (g ^ x), (g ^ y)) = g ^ (x * y)

-- def diffie_hellman_assumption (G : Type) [group G] :=
-- ∀ f : diffie_hellman_candidate G, 

-- def decisional_diffie_hellman_candidate := G × G × G × G → Prop

-- def decisional_diffie_hellman_solution (f : decisional_diffie_hellman_candidate G) :=
-- ∀ (x y : ℕ) (g g' : G), f (g, (g ^ x), (g ^ y), g') = (g' = g ^ (x * y)) 