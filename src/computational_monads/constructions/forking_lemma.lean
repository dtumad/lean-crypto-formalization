import computational_monads.distribution_semantics.prod
import computational_monads.distribution_semantics.option
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.constructions.logging.random_oracle
import computational_monads.simulation_semantics.constructions.logging.seeded_oracle

noncomputable theory

-- TODO: a bunch of random namespace stuff is wierd here
open oracle_comp oracle_spec

open_locale nnreal ennreal big_operators

structure forking_adversary (T U A : Type) [inhabited U]  :=
(adv : oracle_comp (uniform_selecting ++ (T →ₒ U)) A)
(q : ℕ)
(choose_fork : A → query_log (T →ₒ U) → option (fin q))

namespace forking_adversary

variables {T U A : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
  (adv : forking_adversary T U A)

/-- Simulate the adversary, returning a log of the uniform selecting oracle,
  along with the final result and final cache for the random oracle -/
def sim_with_log (adv : forking_adversary T U A) :
  oracle_comp uniform_selecting (option (fin adv.q) × A × query_log uniform_selecting × query_log (T →ₒ U)) :=
do { ⟨x, log, cache, ()⟩ ← default_simulate (logging_oracle _ ++ₛ random_oracle _) adv.adv,
    return (adv.choose_fork x cache, x, log, cache) }

/-- Simulate the adversary, allowing for a seed value to the uniform select oracle,
  and a preset cache value for the random oracle -/
def sim_from_seed (adv : forking_adversary T U A)
  (seed : query_log uniform_selecting) (cache : query_log (T →ₒ U)) :
  oracle_comp uniform_selecting (option (fin adv.q) × A × query_log (T →ₒ U)) :=
do { ⟨x, log, cache, ()⟩ ← simulate (seeded_oracle _ ++ₛ random_oracle _) adv.adv (seed, cache, ()),
  return (adv.choose_fork x cache, x, cache) }

/-- Just simulate to get the resulting `choose_fork` value.
  Implemented as running `simulate_with_log` and throwing out the resulting log and cache -/
def sim_choose_fork (adv : forking_adversary T U A) :
  oracle_comp uniform_selecting (option (fin adv.q)) :=
prod.fst <$> adv.sim_from_seed (query_log.init _) (query_log.init _) 

def advantage (adv : forking_adversary T U A) : ℝ≥0 :=
⦃ λ x, option.is_some x | sim_choose_fork adv ⦄

lemma advantage_eq_tsum (adv : forking_adversary T U A) :
  adv.advantage = ∑' (i : fin adv.q), ⦃sim_choose_fork adv⦄ (some i) :=
distribution_semantics.prob_event_is_some $ sim_choose_fork adv

lemma advantage_eq_sum (adv : forking_adversary T U A) :
  adv.advantage = ∑ i, ⦃sim_choose_fork adv⦄ (some i) :=
trans (advantage_eq_tsum adv) (tsum_fintype _)

end forking_adversary

variables {T U A : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
variables {n : ℕ} (adv : forking_adversary T U A) 

/-- Run computation twice, using the same random information for both,
  responding differently to a query specified by `choose_fork`,
  and returning the results if `choose_fork` makes the same choice each time -/
def fork : oracle_comp uniform_selecting ((option (fin adv.q)) × A × (query_log (T →ₒ U)) × A × (query_log (T →ₒ U))) :=
do {
  -- TODO: I think we want to bundle the next two parts into a single definition above
  ⟨i, x, log, cache⟩ ← adv.sim_with_log,
  -- remove things in the cache after the query we intend to fork on
  forked_cache ← return (cache.fork_cache () (i.map coe)),
  -- run again, using the same random choices for first oracle, and newly forked cache
  ⟨i', x', cache'⟩ ← adv.sim_from_seed log.to_seed forked_cache,
  -- return no forking index unless `fork_cache` gives equal values for both runs.
  -- also return the side outputs and the random oracle cache for both runs
  return ⟨if i = i' then i else none, x, cache, x', cache'⟩
}

/-- TODO: Is this quite right? -/
lemma eval_distribution_fst_map_fork_apply (i : option $ fin adv.q) :
  ⦃prod.fst <$> fork adv⦄ i = ⦃adv.sim_choose_fork ×ₘ adv.sim_choose_fork⦄ (i, i) :=
sorry

section choose_fork

/-- For any non-`none` forking result, `choose_fork` matches for both side outputs -/
lemma choose_fork_eq (i : fin adv.q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : ((some i, x, cache, x', cache')) ∈ (fork adv).support) :
  adv.choose_fork x cache = i ∧ adv.choose_fork x' cache' = i :=
begin
  sorry
  -- simp only [fork, support_bind, set.mem_Union, exists_prop, prod.exists, return_eq_pure,
  --   support_pure_bind, support_pure, set.mem_singleton_iff] at h,
  -- obtain ⟨y, log₀, cache₀, hy, y', cache₀', hy', h⟩ := h,
  
  -- have : adv.choose_fork y cache₀ = adv.choose_fork y' cache₀' := begin
  --   by_contradiction h',
  --   simp only [h', if_false] at h,
  --   exact h
  -- end,
  -- simp only [← this, eq_self_iff_true, if_true] at h,

  -- rw [eq_comm, option.map_eq_some'] at h,
  -- obtain ⟨j, hj, hj'⟩ := h,

  -- simp_rw [prod.eq_iff_fst_eq_snd_eq] at hj',
  -- rw [← hj'.2.1, ← hj'.2.2.1, ← hj'.2.2.2.1, ← hj'.2.2.2.2, ← this, hj, hj'.1],
  -- exact ⟨rfl, rfl⟩,
end

/-- Correctness with respect to `choose_fork`, i.e. the chosen fork matches for both outputs -/
lemma choose_fork_first_eq (i : fin adv.q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : (some i, x, cache, x', cache') ∈ (fork adv).support) :
  adv.choose_fork x cache = i :=
(choose_fork_eq adv i cache cache' x x' h).1

lemma choose_fork_second_eq (i : fin adv.q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : (some i, x, cache, x', cache') ∈ (fork adv).support) :
  adv.choose_fork x' cache' = i :=
(choose_fork_eq adv i cache cache' x x' h).2

end choose_fork

section cache_input

/-- Because of the logging and shared cache both results of fork
  make the same query at the point specified by `choose_fork`.
  TODO: theoretically true for any `j ≤ i`, but not sure that is ever needed? -/
theorem cache_input_same_at_fork (i : fin adv.q) (cache cache' : query_log (T →ₒ U)) (x x' : A)
  (h : ((some i, x, cache, x', cache')) ∈ (fork adv).support) :
  query_log.query_input_same_at cache cache' () i :=
begin
  sorry
end

end cache_input

section fork_success

-- TODO: reverse to standard `≤` notation
lemma prob_fork_eq_some : ⦃ λ out, out.1.is_some | fork adv ⦄ ≥ (adv.advantage ^ 2) / adv.q :=
calc ⦃ λ out, out.1.is_some | fork adv ⦄
  = ⦃ coe ∘ option.is_some | prod.fst <$> fork adv⦄ :
    symm ((distribution_semantics.prob_event_map _ _ _))
  ... = ∑' (j : fin adv.q), (⦃prod.fst <$> fork adv⦄ (some j)) :
    (distribution_semantics.prob_event_is_some $ prod.fst <$> fork adv)
  ... = ∑' (j : fin adv.q), (⦃adv.sim_choose_fork ×ₘ adv.sim_choose_fork⦄ (some j, some j)) :
    sorry --tsum_congr (λ j, congr_arg coe $ eval_distribution_fst_map_fork_apply adv (some j))
  ... = ∑' (j : fin adv.q), (⦃adv.sim_choose_fork⦄ (some j)) ^ 2 :
    by simp only [distribution_semantics.eval_distribution_prod_apply, pow_two, ennreal.coe_mul]
  ... = ∑ j, (⦃adv.sim_choose_fork⦄ (some j)) ^ 2 :
    tsum_fintype _
  ... ≥ (∑ j, ⦃adv.sim_choose_fork⦄ (some j)) ^ 2 / adv.q :
    sorry --le_of_eq_of_le (by rw [finset.card_fin, pow_one]) (ennreal.pow_sum_div_card_le_sum_pow _ _ 1)
  ... = (adv.advantage ^ 2) / adv.q :
    by rw forking_adversary.advantage_eq_sum adv

/- forking algorithm succeeds if a forking point is chosen, and the query outputs differ there -/
def fork_success : option (fin n) × A × query_log (T →ₒ U) × A × query_log (T →ₒ U) → Prop
| ⟨none, _, _, _, _⟩ := false
| ⟨some i, x, cache, x', cache'⟩ := query_log.query_output_diff_at cache cache' () i

/-- Probability that fork success holds is determined by adversary's initial advantage -/
theorem prob_fork_success : ⦃ fork_success | fork adv ⦄
  ≥ ((adv.advantage) ^ 2 / adv.q) - (1 / fintype.card U) :=
calc ⦃fork_success | fork adv⦄
  ≥ (⦃λ out, out.1.is_some | fork adv⦄) * (1 - 1 / fintype.card U) : begin
    -- TODO: this is just an independence statement of the `is_some` and `query_output_diff_at`
    -- Slight complication in that the output diff is only well defined if a `some` index is output
    sorry
  end
  ... ≥ ⦃λ out, out.1.is_some | fork adv⦄ - (1 / fintype.card U) : begin
    -- rw [ennreal.mul_sub sorry, mul_one, mul_div, mul_one, ge_iff_le],
    sorry
  end
  ... ≥ ((adv.advantage) ^ 2 / adv.q) - (1 / fintype.card U) :
    tsub_le_tsub (prob_fork_eq_some adv) le_rfl

end fork_success
