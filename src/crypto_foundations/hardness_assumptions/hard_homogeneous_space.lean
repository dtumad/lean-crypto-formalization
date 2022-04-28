import computational_monads.asymptotics.polynomial_time
import to_mathlib.action_classes

open_locale nnreal ennreal

/-!
# Hard Homogeneous Spaces

This file builds up the definition of a hard homogeneous space.

`algorithmic_homogeneous_space` further requires the group action and group operations are efficiently computable.
`hard_homogeneous_space` further requires vectorization and parallelization are hard.
-/

open oracle_comp

structure algorithmic_homogenous_space {G X : Type} [fintype G] [add_group G] [add_action G X]
  [decidable_eq G] [decidable_eq X]
  extends principal_action_class G X :=
(poly_time_add : poly_time (λ x, x.1 + x.2 : G × G → G))
(poly_time_inv : poly_time (λ x, -x : G → G))
(poly_time_vadd : poly_time (λ x, x.1 +ᵥ x.2 : G × X → X))
(poly_time_eq_G : poly_time (λ x, x.1 = x.2 : G × G → bool))
(poly_time_eq_X : poly_time (λ x, x.1 = x.2 : X × X → bool))
(poly_time_rnd_G : poly_time_oracle_comp (λ _, uniform_select_fintype G : unit → oracle_comp oracle_spec.uniform_selecting G))

-- section computational_advantages

-- variables {G X : Type} [fintype G] [fintype X] 
--   [inhabited G] [inhabited X] 
--   [decidable_eq X] [decidable_eq G]
-- variables [add_monoid G] [add_action G X] [principal_action_class G X]

-- /-- Analogue of Discrete-logarithm asumption game -/
-- noncomputable def vectorization_experiment (A : X × X → prob_comp G) : prob_comp bool :=
-- do{ x₁ ← $ᵗ X, x₂ ← $ᵗ X,
--     g ← A (x₁, x₂),
--     return (g = vectorization G x₁ x₂) }

-- /-- Vectorization advantage of an adversary in the vectorization experiment. -/
-- noncomputable def vectorization_advantage (adversary : X × X → prob_comp G) : ℝ≥0∞ :=
-- (vectorization_experiment adversary).prob_success
--   - (vectorization_experiment (λ (_ : X × X), $ᵗ G)).prob_success

-- variable (G)

-- /-- Analogue of the decisional Diffie-Helman experiment -/
-- noncomputable def parallelization_experiment (A : X × X × X → prob_comp X) : prob_comp bool :=
-- do{ x₁ ←$ᵗ X,
--     x₂ ←$ᵗ X,
--     x₃ ←$ᵗ X,
--     x₄ ← A (x₁, x₂, x₃),
--     return ((vectorization G x₂ x₁) = (vectorization G x₄ x₃)) }

-- /-- Parallelization advantage of an adversary in parallelization experiment -/
-- noncomputable def parallelization_advantage (adversary : X × X × X → prob_comp X) : ℝ≥0∞ :=
-- (parallelization_experiment G adversary).prob_success
--   - (parallelization_experiment G (λ (_ : X × X × X), $ᵗ X)).prob_success

-- end computational_advantages

-- section algorithmic_homogenous_space

-- -- Note we moved from `add_monoid` to `add_comm_group` to match standard defintiions
-- -- TODO: Could just derive instances on `G` from instances on `X`? doesn't change much
-- /-- TODO: Use this version instead. -/
-- class alg_homogenous_space (G X : Type)
--   [fintype G] [fintype X] [inhabited G] [inhabited X]
--   [decidable_eq X] [decidable_eq G]
--   [add_comm_group G] [add_action G X]
--   extends principal_action_class G X :=
-- (poly_time_add : poly_time (λ x, x.1 + x.2 : G × G → G))
-- (poly_time_inv : poly_time (λ x, -x : G → G))
-- (poly_time_vadd : poly_time (λ x, x.1 +ᵥ x.2 : G × X → X))
-- (poly_time_eq_G : poly_time (λ x, x.1 = x.2 : G × G → bool))
-- (poly_time_eq_X : poly_time (λ x, x.1 = x.2 : X × X → bool))
-- (poly_time_rnd_G : prob_poly_time (λ _, $ᵗ G : unit → prob_comp G))

-- /-- algorithmic homogenous space parameterized by a set up public parameters and a `setup` algorithm.
--   Hardness assumptions are given relative to 
-- TODO: This is really tedious to have this many typeclasses
-- TODO: Use this version -/
-- class har_homogenous_space {public_parameters : Type} (G X : public_parameters → Type)
--   [∀ p, fintype $ G p] [∀ p, fintype $ X p] [∀ p, inhabited $ G p] [∀ p, inhabited $ X p]
--   [∀ p, decidable_eq $ X p] [∀ p, decidable_eq $ G p]
--   [∀ p, add_comm_group $ G p] [∀ p, add_action (G p) (X p)]
--   [∀ p, alg_homogenous_space (G p) (X p)] :=
-- (setup : ℕ → prob_comp public_parameters)
-- (poly_time_setup : prob_poly_time setup)
-- (vectorization_hard : 
--   ∀ (A : Π p, X p × X p → prob_comp (G p))
--     (hA : ∀ p, prob_poly_time (A p)),
--   negligable (λ sp, prob_comp.prob_success $ do {
--     p ← setup sp,
--     vectorization_experiment (A p)
--   })
-- )
-- (parallelization_hard :
--   ∀ (A : Π p, X p × X p × X p → prob_comp (X p))
--     (hA : ∀ p, prob_poly_time (A p)),
--   negligable (λ sp, prob_comp.prob_success $ do {
--     p ← setup sp,
--     parallelization_experiment (G p) (A p)
--   })
-- )

-- end algorithmic_homogenous_space

-- section hard_homogeneous_space

-- variables [function_cost_model ℚ] [comp_cost_model ℚ]
-- variables (G X : ℕ → Type) 
--   [∀ n, fintype (G n)] [∀ n, fintype (X n)]
--   [∀ n, inhabited (G n)] [∀ n, inhabited (X n)]
--   [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)]
--   [∀ n, add_comm_group (G n)] [∀ n, add_action (G n) (X n)]
--   [∀ n, principal_action_class (G n) (X n)]

-- /-- A homogenous space is defined by a parameterized collection of homogenous spaces (`principal_action_class`).
--   `G` and `X` together define a generation algorithm for homogenous spaces from a security parameter,
--     and we want the following operations to have polynomial-growth time in the security parameter.

--   Note that we model `G n` and `X n` as having some *fixed* internal representation,
--     so this definition doesn't include functions for converting to and from representative bit-strings.
--   TODO: clean up the many typeclass dependencies -/
-- class algorithmic_homogeneous_space :=
-- (polynomial_complexity_add : 
--   complexity_class.polynomial_complexity (λ sp, (λ x, x.1 + x.2 : G sp × G sp → G sp)))
-- (polynomial_complexity_inv :
--   complexity_class.polynomial_complexity (λ sp, (λ x, -x : G sp → G sp)))
-- (polynomial_complexity_vadd : 
--   complexity_class.polynomial_complexity (λ n, (λ x, x.1 +ᵥ x.2 : G n × X n → X n)))
-- (polynomial_complexity_eq_G : 
--   complexity_class.polynomial_complexity (λ n, (λ x, x.1 = x.2 : G n × G n → Prop)))
-- (polynomial_complexity_eq_X : 
--   complexity_class.polynomial_complexity (λ n, (λ x, x.1 = x.2 : X n × X n → Prop)))
-- (polynomial_complexity_rnd_G : 
--   complexity_class.polynomial_complexity (λ n, (λ x, $ᵗ (G n) : unit → prob_comp (G n))))

-- section algorithmic_homogeneous_space

-- -- -- TODO: derive rnd X efficient by choosing a generator and using G_rnd_efficient
-- lemma polynomial_complexity_rnd_X [h : algorithmic_homogeneous_space G X] 
--   [pairing_cost_extension ℚ] : 
--   complexity_class.polynomial_complexity (λ n, (λ x, $ᵗ (X n) : unit → prob_comp (X n))) :=
-- begin
--   have : complexity_class.polynomial_complexity
--     (λ n, (λ x, do {
--       g ← $ᵗ (G n),
--       return (g +ᵥ (default))
--     } : unit → prob_comp (X n))),
--   { refine complexity_class.polynomial_complexity_comp_bind _ _,
--     refine algorithmic_homogeneous_space.polynomial_complexity_rnd_G X,
--     refine complexity_class.polynomial_complexity_comp_unit_prod _ _,
--     refine complexity_class.polynomial_complexity_comp_ret_of_polynomial_complexity _,
--     exact complexity_class.polynomial_complexity_comp_ext 
--       (complexity_class.polynomial_complexity_of_has_cost_zero (λ n, (λ g, (g, default) : G n → G n × X n))) 
--       (h.polynomial_complexity_vadd) (by simp) },
      
--   refine complexity_class.polynomial_complexity_comp_ext' (λ n _, _) this,
--   refine pmf.ext (λ x, _),
--   simp,
--   refine trans (tsum_congr (λ g, _)) (tsum_ite_eq (vectorization (G n) (default) x) _),
--   simp_rw [eq_vectorization_iff],
--   sorry,
--   -- refine congr (congr (by congr) _) _,
--   -- simpa using principal_action_class.fintype_card_eq (G n) (X n),
-- end

-- end algorithmic_homogeneous_space

-- structure vectorization_adversary (G X : ℕ → Type) :=
-- (A : Π sp, X sp × X sp → prob_comp (G sp))
-- (polynomial_complexity : complexity_class.polynomial_complexity A)

-- structure parallelization_adversary (X : ℕ → Type) :=
-- (A : Π sp, X sp × X sp × X sp → prob_comp (X sp))
-- (polynomial_complexity : complexity_class.polynomial_complexity A)

-- example : comm_semiring ℝ≥0 := by apply_instance

-- /-- Extension of `algorithmic_homogenous_space` with hardness assumptions.
--   Vectorization and parallelization correspond to discrete-log and Diffie-Hellman -/
-- class hard_homogeneous_space extends algorithmic_homogeneous_space G X :=
-- (vectorization_hard : ∀ (adv : vectorization_adversary G X),
--   negligable (λ sp, vectorization_advantage (adv.A sp)))
-- (parallelization_hard : ∀ (adv : parallelization_adversary X),
--   negligable (λ sp, parallelization_advantage (G sp) (adv.A sp)))

-- end hard_homogeneous_space
