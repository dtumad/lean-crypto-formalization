import computational_monads.simulation_semantics.simulation_oracles
import computational_monads.constructions.uniform_select
import computational_monads.asymptotics.queries_at_most
import computational_monads.distribution_semantics.eval_distribution

noncomputable theory

open oracle_comp oracle_spec

open_locale nnreal ennreal

variables {T U A : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]

variables (adversary : oracle_comp (uniform_selecting ++ (T →ₒ U)) A)
  {q : ℕ} --(hq : queries_at_most adversary q)
  (choose_fork : A → query_log (T →ₒ U) → option (fin q))

/-- Simulation oracle for forking algorithm.
  Log the uniform selection oracle and cache the random outputs of the forked oracle -/
def fork_sim : simulation_oracle (uniform_selecting ++ (T →ₒ U)) uniform_selecting :=
(logging_simulation_oracle uniform_selecting) ⟪++⟫
  (random_simulation_oracle (T →ₒ U) ∘ₛ (caching_simulation_oracle (T →ₒ U)))

def fork_sim' : simulation_oracle (uniform_selecting ++ (T →ₒ U)) uniform_selecting :=
(seeded_simulation_oracle uniform_selecting) ⟪++⟫
  (random_simulation_oracle (T →ₒ U) ∘ₛ (caching_simulation_oracle (T →ₒ U)))

/-- Remove parts of the cache after the query chosen to fork on
  TODO: might need to reverse this first? (double check) otherwise build that into a lower API -/
def fork_cache : (option $ fin q) → query_log (T →ₒ U) → query_log (T →ₒ U)
:= sorry

/-- Run computation twice, using the same random information for both,
  responding differently to a query specified by `choose_fork`,
  and returning the results if `choose_fork` makes the same choice each time -/
def fork : oracle_comp uniform_selecting (option $ (fin q) × A × (query_log (T →ₒ U)) × A × (query_log (T →ₒ U))) :=
do {
  -- run the adversary normally, logging the first oracle and caching the second
  ⟨x, ⟨log, ⟨cache, ()⟩⟩⟩ ← (simulate fork_sim adversary (query_log.init _, (query_log.init _, ()))),
  -- choose the index of the query to fork on
  i ← return (choose_fork x cache),
  -- remove things in the cache after the forking query
  forked_cache ← return (fork_cache i cache),
  -- run again, using the same random choices for first oracle, and forked cache
  ⟨x', ⟨_, ⟨cache', ()⟩⟩⟩ ← (simulate fork_sim' adversary (log.to_seed, (forked_cache, ()))),
  -- check the forking index for the second result
  i' ← return (choose_fork x' cache'),
  -- return a value if both runs choose the same cache value and where successful (not `none`)
  -- TODO: maybe some of this pre-checking should be different?
  --        wouldn't even need to return an option if we just put this in the success pred?
  return (if i ≠ none ∧ i = i' then i.map (λ n, (n, x, cache, x', cache')) else none)
}

/-- Because of the logging and shared cache, both results of fork make the same query if the result succeeds -/
lemma cache_same_at (n : fin q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : (some (n, x, cache, x', cache')) ∈ (fork adversary choose_fork).support) :
  ((cache ()).nth n).map prod.fst = ((cache ()).nth n).map prod.fst :=
sorry

-- Correctness with respect to `choose_fork`, i.e. `i` and is the result for both calls
-- For signature will correspond to both signatures being valid
lemma mem_choose_fork (n : fin q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : (some (n, x, cache, x', cache')) ∈ (fork adversary choose_fork).support) :
  choose_fork x cache = n ∧ choose_fork x' cache' = n :=
sorry

def accepting_experiment : oracle_comp uniform_selecting (option $ fin q) :=
do {
  (x, ⟨log, ⟨cache, ()⟩⟩) ← simulate fork_sim (adversary) (query_log.init _, (query_log.init _, ())),
  return (choose_fork x cache)
}

-- Adversary succeeds wrt the choose_fork function
def accepting_prob : ℝ≥0∞ := ⟦ coe ∘ option.is_some | accepting_experiment adversary choose_fork ⟧

-- query_results are different for the two caches at `n`
def query_output_diff_at (n : fin q) (cache cache' : query_log (T →ₒ U)) : Prop :=
  ((cache ()).nth n).map prod.snd ≠ ((cache' ()).nth n).map prod.snd

-- forking algorithm succeeds if both `choose_fork` calls return the same success value
--    (captured in `fork` already by the `i ≠ none ∧ i = i'` clause)
-- and also the query results for the `i`th thing in the cache are distinct
def fork_success : option (fin q × A × query_log (T →ₒ U) × A × query_log (T →ₒ U)) → Prop
| none := false
| (some ⟨n, x, cache, x', cache'⟩) :=
    ((cache ()).nth n).map prod.snd ≠ ((cache' ()).nth n).map prod.snd

-- Probability that both adversaries have the same `choose_fork` result, and that the they correspond to distinct query results.
-- For signature will correspond to both signatures being on different hash result values
-- Sort of the "meat" of the forking lemma
lemma prob_fork_success :
  ⟦ fork_success | fork adversary choose_fork ⟧
    ≥ (((accepting_prob adversary choose_fork) ^ 2 / q) - (1 / fintype.card U)) :=
sorry
