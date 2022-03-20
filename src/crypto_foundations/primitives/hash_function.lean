-- import computational_complexity.complexity_class
-- import computational_monads.constructions

-- variables [function_cost_model ℚ] [comp_cost_model ℚ]

-- /-!
-- # Hash Functions

-- This file defines the notion of a keyed hash function.

-- TODO: Think about using `encodable` type-class for `I` and maybe `O`
-- -/
-- structure hash_function (K I O : Type) :=
-- (keygen : unit → prob_comp K)
-- (hash : K × I → O)

-- namespace hash_function

-- variables {K I O : Type} (h : hash_function K I O)

-- variables [decidable_eq O]

-- /-- The security game for collision resistance as a probabalistic function. -/
-- def collision_finding_experiment (h : hash_function K I O)
--   (A : K → prob_comp (I × I)) : prob_comp bool := 
-- do{ k ← (h.keygen ()),
--     xs ← (A k),
--     return (h.hash (k, xs.1) = h.hash (k, xs.2)) }

-- end hash_function

-- /-- `keygen` takes in a security parameter and outputs a key bundled with the parameter
--   `hash` takes a `hash_key` from keygen and a string in the input space to a string in the output space
--   TODO: Use better complexity model and public parameters model for this -/
-- structure hash_scheme (K I O : ℕ → Type) :=
-- (scheme (sp : ℕ) : hash_function (K sp) (I sp) (O sp))
-- (keygen_poly_time : complexity_class.polynomial_complexity (λ sp, (scheme sp).keygen))
-- (hash_poly_time : complexity_class.polynomial_complexity (λ sp, (scheme sp).hash))

-- namespace hash_scheme

-- variables {K I O : ℕ → Type} {H : hash_scheme K I O}

-- section projections

-- variable (H)

-- def keygen (sp : ℕ) : prob_comp (K sp) :=
-- (H.scheme sp).keygen ()

-- @[simp]
-- lemma keygen_eq (sp : ℕ) :
--   H.keygen sp = (H.scheme sp).keygen () := rfl

-- def hash {sp : ℕ} (k : K sp) (i : I sp) : O sp :=
-- (H.scheme sp).hash (k, i)

-- @[simp]
-- lemma hash_eq {sp : ℕ} (k : K sp) (i : I sp) :
--   H.hash k i = (H.scheme sp).hash (k, i) := rfl

-- end projections

-- variables [∀ n, decidable_eq $ O n]

-- structure collision_finding_adversary (H : hash_scheme K I O) :=
-- (adv : Π (sp : ℕ), K sp → prob_comp ((I sp) × (I sp)))
-- (pt : complexity_class.polynomial_complexity adv)

-- def collision_resistant (H : hash_scheme K I O) : Prop :=
-- ∀ (A : collision_finding_adversary H),
-- negligable (λ sp, 
--   ((H.scheme sp).collision_finding_experiment (A.adv sp)).prob_success)

-- end hash_scheme