-- import computational_monads.probabalistic_computation.constructions
-- import computational_monads.oracle_access.oracle_comp

-- open_locale nnreal ennreal

-- noncomputable theory

-- namespace oracle_comp

-- variables {T U A X : Type} [decidable_eq T] [fintype U] [nonempty U] [decidable_eq U]

-- def accepting_exp
--   (adv : X → oracle_comp ⟦T →ᵒ U⟧ A)
--   (query_to_fork : A → T) :
--   X → prob_comp (A × (T × U)) :=
-- λ x, simulate_result (random_oracle T U) [] (do {
--   a ← adv x,
--   t ← return (query_to_fork a),
--   u ← query () t,
--   return (a, (t, u))
-- })

-- def accepting_probability (input_generator : prob_comp X)
--   (adv : X → oracle_comp ⟦T →ᵒ U⟧ A)
--   (query_to_fork : A → T)
--   (validate : A × (T × U) → prob_comp bool) : ℝ≥0∞ :=
-- prob_comp.prob_success (do {
--   x ← input_generator,
--   (a, (t, u)) ← (accepting_exp adv query_to_fork x),
--   val ← validate (a, (t, u)),
--   return val
-- })

-- constant fork (adv : X → oracle_comp ⟦T →ᵒ U⟧ A)
--   (query_to_fork : A → T) :
--   X → prob_comp ((A × (T × U)) × (A × (T × U)))

-- def forking_probability (input_generator : prob_comp X)
--   (adv : X → oracle_comp ⟦T →ᵒ U⟧ A)
--   (query_to_fork : A → T)
--   (validate : A × (T × U) → prob_comp bool) : ℝ≥0∞ :=
-- prob_comp.prob_success (do {
--   x ← input_generator,
--   ((a, (t, u)), (a', (t', u'))) ← fork adv query_to_fork x,
--   val ← validate (a, (t, u)),
--   val' ← validate (a', (t', u')),
--   return (t = t' ∧ u ≠ u' ∧ val ∧ val')
-- })

-- axiom forking_lemma (input_generator : prob_comp X)
--   (adv : X → oracle_comp ⟦T →ᵒ U⟧ A) (query_to_fork : A → T)
--   (validate : A × (T × U) → prob_comp bool)
--   (q : ℕ) (hq : ∀ x, queries_at_most (adv x) q) :
--     let frk := forking_probability input_generator adv query_to_fork validate in
--     let acc := accepting_probability input_generator adv query_to_fork validate in
--     frk ≥ acc * (acc / q - 1 / fintype.card U)


-- end oracle_comp


-- end prob_comp 