import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.oracle_compose
import computational_monads.constructions.uniform_select
import computational_monads.asymptotics.queries_at_most
import computational_monads.distribution_semantics.prob_event
import computational_monads.simulation_semantics.constructions.logging.caching_oracle

noncomputable theory

open oracle_comp oracle_spec

open_locale nnreal ennreal

structure forking_adversary (T U A : Type) [inhabited U]  :=
(adv : oracle_comp (uniform_selecting ++ (T →ₒ U)) A)
(q : ℕ)
(choose_fork : A → query_log (T →ₒ U) → option (fin q))

namespace forking_adversary

variables {T U A : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
  (adv : forking_adversary T U A)

/-- Simulate the adversary, returning a log of the uniform selecting oracle,
  along with the final result and final cache for the random oracle -/
def simulate_with_log (adv : forking_adversary T U A) :
  oracle_comp uniform_selecting (A × query_log uniform_selecting × query_log (T →ₒ U)) :=
do { ⟨a, log, cache, ()⟩ ← simulate (logging_oracle _ ⟪++⟫ random_oracle _) adv.adv
      (query_log.init _, query_log.init _, ()),
    return (a, log,cache) }

/-- Simulate the adversary, allowing for a seed value to the uniform select oracle,
  and a preset cache value for the random oracle -/
def simulate_from_seed (adv : forking_adversary T U A)
  (seed : query_log uniform_selecting) (cache : query_log (T →ₒ U)) :
  oracle_comp uniform_selecting (A × query_log (T →ₒ U)) :=
do { ⟨a, log, cache, ()⟩ ← simulate (seeded_oracle _ ⟪++⟫ random_oracle _) adv.adv (seed, cache, ()),
  return (a, cache) }

/-- Most basic definition of simulation that just returns the result,
  and the final cache value of the random oracle, without the `uniform_selecting` log -/
def simulate_basic (adv : forking_adversary T U A) :
  oracle_comp uniform_selecting (A × query_log (T →ₒ U)) :=
simulate_from_seed adv (query_log.init _) (query_log.init _)

def accepting_experiment (adv : forking_adversary T U A) :
  oracle_comp uniform_selecting (option (fin adv.q)) :=
do { ⟨a, log, cache⟩ ← adv.simulate_with_log,
  return (adv.choose_fork a cache) }

def advantage (adv : forking_adversary T U A) : ℝ≥0∞ :=
⟦ λ x, option.is_some x | accepting_experiment adv ⟧

end forking_adversary

variables {T U A : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
variables {n : ℕ} (adv : forking_adversary T U A) 

/-- Run computation twice, using the same random information for both,
  responding differently to a query specified by `choose_fork`,
  and returning the results if `choose_fork` makes the same choice each time -/
def fork : oracle_comp uniform_selecting (option $ (fin adv.q) × A × (query_log (T →ₒ U)) × A × (query_log (T →ₒ U))) :=
do {
  ⟨x, ⟨log, cache⟩⟩ ← adv.simulate_with_log,
  i ← return (adv.choose_fork x cache),
  -- remove things in the cache after the forking query
  forked_cache ← return (cache.fork_cache () (i.map coe)),
  -- run again, using the same random choices for first oracle, and forked cache
  ⟨x', cache'⟩ ← adv.simulate_from_seed log.to_seed forked_cache,
  i' ← return (adv.choose_fork x' cache'),
  -- return a value if both runs choose the same cache value and where successful (not `none`)
  -- the result will be `none` if indexes don't match or are already `none`
  return (if i = i' then i.map (λ j, (j, x, cache, x', cache')) else none)
}

/-- Correctness with respect to `choose_fork`, i.e. the chosen fork matches for both outputs -/
lemma choose_fork_first_eq (i : fin adv.q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : (some (i, x, cache, x', cache')) ∈ (fork adv).support) :
  adv.choose_fork x cache = i :=
begin
  simp only [fork, support_bind, set.mem_Union, exists_prop, prod.exists, return_eq_pure,
    support_pure_bind, support_pure, set.mem_singleton_iff] at h,
  obtain ⟨y, log₀, cache₀, hy, y', cache₀', hy', h⟩ := h,
  
  have : adv.choose_fork y cache₀ = adv.choose_fork y' cache₀' := begin
    by_contradiction h',
    simp only [h', if_false] at h,
    exact h
  end,
  simp only [← this, eq_self_iff_true, if_true] at h,

  rw [eq_comm, option.map_eq_some'] at h,
  obtain ⟨j, hj, hj'⟩ := h,

  simp_rw [prod.eq_iff_fst_eq_snd_eq] at hj',

  have hy : x = y := hj'.2.1.symm,
  have hcache₀ : cache = cache₀ := hj'.2.2.1.symm,

  rw [hy, hcache₀, hj],
  exact congr_arg option.some hj'.1,
end

lemma choose_fork_second_eq (i : fin adv.q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : (some (i, x, cache, x', cache')) ∈ (fork adv).support) :
  adv.choose_fork x' cache' = i :=
begin
  simp only [fork, support_bind, set.mem_Union, exists_prop, prod.exists, return_eq_pure,
    support_pure_bind, support_pure, set.mem_singleton_iff] at h,
  obtain ⟨y, log₀, cache₀, hy, y', cache₀', hy', h⟩ := h,
  
  have : adv.choose_fork y cache₀ = adv.choose_fork y' cache₀' := begin
    by_contradiction h',
    simp only [h', if_false] at h,
    exact h
  end,
  simp only [this, eq_self_iff_true, if_true] at h,

  rw [eq_comm, option.map_eq_some'] at h,
  obtain ⟨j, hj, hj'⟩ := h,

  simp_rw [prod.eq_iff_fst_eq_snd_eq] at hj',

  have hy : x' = y' := hj'.2.2.2.1.symm,
  have hcache₀ : cache' = cache₀' := hj'.2.2.2.2.symm,

  rw [hy, hcache₀, hj],
  exact congr_arg option.some hj'.1,
end

/-- Because of the logging and shared cache both results of fork
  make the same query at the point where the fork was chosen -/
lemma cache_input_same_at_fork (i : fin adv.q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : (some (i, x, cache, x', cache')) ∈ (fork adv).support) :
  query_log.query_input_same_at cache cache' () i :=
begin
  sorry
end

/- forking algorithm succeeds if a forking point is chosen,  -/
def fork_success : option (fin n × A × query_log (T →ₒ U) × A × query_log (T →ₒ U)) → Prop
| none := false
| (some ⟨i, x, cache, x', cache'⟩) := query_log.query_output_diff_at cache cache' () i

/-- Probability that 
-- For signature will correspond to both signatures being on different hash result values
-- Sort of the "meat" of the forking lemma -/
lemma prob_fork_success : ⟦ fork_success | fork adv ⟧
  ≥ ((adv.advantage) ^ 2 / adv.q) - (1 / fintype.card U) :=
sorry
