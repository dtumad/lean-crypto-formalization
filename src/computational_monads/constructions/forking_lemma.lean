import computational_monads.simulation_semantics.simulation_oracles
import computational_monads.constructions.uniform_select

open oracle_comp oracle_spec

@[inline, reducible]
def fork_spec (T U : Type) [inhabited U] :
  oracle_spec := uniform_selecting ++ (T →ₒ U)

noncomputable def fork_sim {T U A : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
  (adversary : oracle_comp (fork_spec T U) A)
  (seed : query_log (fork_spec T U)) :
  oracle_comp uniform_selecting (A × query_log (fork_spec T U)) :=
(simulate (((simulate_right $ random_simulation_oracle (T →ₒ U))
  ∘ₛ (caching_simulation_oracle _))) adversary ([], ((), ())))
    >>= λ ⟨a, log, _, _⟩, return (a, log)

noncomputable def fork {T U A : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
  (adversary : oracle_comp (uniform_selecting ++ (T →ₒ U)) A)
  (fork_pred : A → T × U) :
  oracle_comp uniform_selecting (option $ A × A) :=
begin
  -- let spec := uniform_selecting ++ (T →ₒ U),
  let := ((simulate_right $ random_simulation_oracle (T →ₒ U))
    ∘ₛ (caching_simulation_oracle _)),
  refine do {
    ⟨a, log⟩ ← fork_sim adversary [],

    ⟨t, u⟩ ← return (fork_pred a),
    v ← return (query_log.lookup log (sum.inr ()) t),

    log_pre_fork ← return log,

    ⟨a', log'⟩ ← fork_sim adversary log_pre_fork,
    ⟨t', u'⟩ ← return (fork_pred a'),

    return ((a, a'))
  },
end




-- import computational_monads.constructions
-- import computational_monads.oracle_comp

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