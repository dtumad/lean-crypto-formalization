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
| none log := []
| (some n) log := log.reverse.take ↑n

/-- Run computation twice, using the same random information for both,
  responding differently to a query specified by `choose_fork`,
  and returning the results if `choose_fork` makes the same choice each time -/
def fork : oracle_comp uniform_selecting (option $ (fin q) × A × (query_log (T →ₒ U)) × A × (query_log (T →ₒ U))) :=
do {
  -- run the adversary normally, logging the first oracle and caching the second
  ⟨x, ⟨log, ⟨cache, ()⟩⟩⟩ ← (simulate fork_sim adversary ([], ([], ()))),
  -- choose the index of the query to fork on
  i ← return (choose_fork x cache),
  -- remove things in the cache after the forking query
  forked_cache ← return (fork_cache i cache),
  -- run again, using the same random choices for first oracle, and forked cache
  ⟨x', ⟨_, ⟨cache', ()⟩⟩⟩ ← (simulate fork_sim' adversary (log.reverse, (forked_cache, ()))),
  -- check the forking index for the second result
  i' ← return (choose_fork x' cache'),
  -- return a value if both runs choose the same cache value and where successful (not `none`)
  return (if i ≠ none ∧ i = i' then i.map (λ n, (n, x, cache, x', cache')) else none)
}

/-- `n`th position in both caches has the same input and different outputs-/
def cache_same_in_diff_out (n : ℕ) (cache : query_log (T →ₒ U)) (cache' : query_log (T →ₒ U)) : Prop :=
match (cache.nth n, cache'.nth n) with
| ((some ⟨(), t, u⟩), (some ⟨(), t', u'⟩)) := t = t' ∧ u ≠ u'
| _ := false
end

section probabilities

-- TODO: random extra things floating around from random_simulation_oracle
/--
  Run the adversary and then return the result of what should be forked on.
  If `choose_fork` returns `none` then adversary failed (e.g. an invalid signature in unforgability experiment).
  Otherwise `choose_fork` returns the index of query that the output should correspond to -/
def acc_experiment : oracle_comp uniform_selecting (option (fin q)) :=
do {
  ⟨x, ⟨log, ⟨cache, ()⟩⟩⟩ ← (simulate fork_sim adversary ([], ([], ()))),
  return (choose_fork x cache)
}

/-- Chance that the pre-fork algorithm has a positive result with `choose_fork` -/
def acc_prob : ℝ≥0∞ := ⟦ (≠) none | acc_experiment adversary choose_fork ⟧

/- successfully got two caches, two adversary outputs, and and integer `n`,
  such that `choose_fork` given `n` for both outputs, and the `n`th position in cache has the same inputs and different outputs.
  Being the result of `choose_fork` should give that the result is a valid signature or whatever.
-/
def fork_success (fork_result : option $ (fin q) × A × (query_log (T →ₒ U)) × A × (query_log (T →ₒ U))) : Prop :=
match fork_result with
| none := false
| (some ⟨n, x, cache, x', cache'⟩) := cache_same_in_diff_out n cache cache'
    ∧ some n = choose_fork x cache ∧ some n = choose_fork x' cache'
end

/-- Chance of forking algorithm being successful -/
def frk_prob : ℝ≥0∞ := ⟦ fork_success choose_fork | fork adversary choose_fork ⟧

end probabilities