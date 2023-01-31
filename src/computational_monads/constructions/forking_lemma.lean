/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.constructions.product
import computational_monads.distribution_semantics.option
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.constructions.logging.random_oracle
import computational_monads.simulation_semantics.constructions.logging.seeded_oracle
import computational_monads.simulation_semantics.constructions.identity_oracle

/-!
# Forking Lemma for Oracle Computations

This file defines a version of the forking lemma, constructing a computation
that "rewinds" a computation to a particular query, and then reruns it.
The result is a pair of outputs, for which the beginning of the corresponding
computations match, in terms of the queries logged to the oracles.
-/

noncomputable theory

open oracle_comp oracle_spec

open_locale nnreal ennreal big_operators

structure forking_adversary (T U α : Type) [inhabited U] [fintype U]
  [decidable_eq T] [decidable_eq U] :=
(adv : oracle_comp (uniform_selecting ++ (T ↦ₒ U)) α) (q : ℕ)
-- Given an output and a random oracle cache, decide which part of cache should be forked.
(choose_fork : α → query_log (T ↦ₒ U) → option (fin q))
-- The adversary always makes at least one query to the random oracle.
(cache_nonempty : ∀ (a : α) (cache : query_log (T ↦ₒ U)),
  (a, (), cache) ∈ (default_simulate (idₛ ++ₛ random_oracle _) adv).support →
  ¬ (cache ()).empty)
-- If choose fork result isn't `none`, the chosen index corresponds to an actual cache entry.
(no_overflow : ∀ (a : α) (cache : query_log (T ↦ₒ U)) (i : fin q), choose_fork a cache = some i →
  (a, (), cache) ∈ (default_simulate (idₛ ++ₛ random_oracle _) adv).support →
  ↑i < (cache ()).length)

namespace forking_adversary

variables {T U α : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
  (adv : forking_adversary T U α)

section simulate_choose_fork

/-- Just simulate to get the resulting `choose_fork` value.
  Implemented as running `simulate_with_log` and throwing out the resulting log and cache -/
def simulate_choose_fork (adv : forking_adversary T U α) :
  oracle_comp uniform_selecting (option (fin adv.q)) :=
do{ ⟨x, log, cache⟩ ← default_simulate (logging_oracle _ ++ₛ random_oracle _) adv.adv,
    return (adv.choose_fork x cache) }

end simulate_choose_fork

section simulate_with_log

/-- Simulate the adversary, returning a log of the uniform selecting oracle,
  along with the final result and final cache for the random oracle -/
def simulate_with_log (adv : forking_adversary T U α) : oracle_comp uniform_selecting
  (option (fin adv.q) × α × query_log uniform_selecting × query_log (T ↦ₒ U)) :=
do{ ⟨x, log, cache⟩ ← default_simulate (logging_oracle _ ++ₛ random_oracle _) adv.adv,
    return (adv.choose_fork x cache, x, log, cache) }

variables (o : option (fin adv.q) × α × query_log uniform_selecting × query_log (T ↦ₒ U))



end simulate_with_log

section simulate_from_seed

/-- Simulate the adversary, allowing for a seed value to the uniform select oracle,
  and a preset cache value for the random oracle, returning the final cache -/
def simulate_from_seed (adv : forking_adversary T U α)
  (seed : query_log uniform_selecting) (cache : query_log (T ↦ₒ U)) :
  oracle_comp uniform_selecting (option (fin adv.q) × α × query_log (T ↦ₒ U)) :=
do { ⟨x, log, cache⟩ ← simulate (seeded_oracle _ ++ₛ random_oracle _) adv.adv (seed, cache),
  return (adv.choose_fork x cache, x, cache) }

end simulate_from_seed

section advantage

def advantage (adv : forking_adversary T U α) : ℝ≥0∞ :=
⁅ λ x, option.is_some x | simulate_choose_fork adv ⁆

lemma advantage_eq_tsum (adv : forking_adversary T U α) :
  adv.advantage = ∑' (i : fin adv.q), ⁅simulate_choose_fork adv⁆ (some i) :=
prob_event_is_some $ simulate_choose_fork adv

lemma advantage_eq_sum (adv : forking_adversary T U α) :
  adv.advantage = ∑ i, ⁅simulate_choose_fork adv⁆ (some i) :=
trans (advantage_eq_tsum adv) (tsum_fintype _)

end advantage

end forking_adversary

variables {T U α : Type} [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U]
  [decidable_eq α] {n : ℕ} (adv : forking_adversary T U α)

/-- Run computation twice, using the same random information for both,
  responding differently to a query specified by `choose_fork`,
  and returning the results if `choose_fork` makes the same choice each time -/
def fork (adv : forking_adversary T U α) : oracle_comp uniform_selecting
  ((option (fin adv.q)) × α × (query_log (T ↦ₒ U)) × α × (query_log (T ↦ₒ U))) :=
do{ -- run the adversary for the first time, logging coins and caching random oracles
    ⟨i, ⟨x, ⟨log, cache⟩⟩⟩ ← adv.simulate_with_log,
    -- run again, using the same random choices for first oracle, and newly forked cache
    -- TODO: might be off by one error with forking somewhere along the way?
    ⟨i', x', cache'⟩ ← adv.simulate_from_seed log.to_seed (cache.fork_cache () (i.map coe)),
    -- return no forking index unless `fork_cache` gives equal values for both runs.
    -- also return the side outputs and the random oracle cache for both runs
    return ⟨if i = i' then i else none, x, cache, x', cache'⟩ }

/-- Definition without the match functions used in the original definition -/
lemma fork_def : fork adv = do {o ← adv.simulate_with_log,
  o' ← adv.simulate_from_seed o.2.2.1.to_seed ((o.2.2.2.fork_cache () (o.1.map coe))),
  return (if o.1 = o'.1 then o.1 else none, o.2.1, o.2.2.2, o'.2.1, o'.2.2)} :=
begin
  unfold fork,
  congr, ext o, rcases o with ⟨i, x, log, cache⟩, rw [fork._match_2],
  congr, ext o', rcases o' with ⟨i', x', cache'⟩, rw [fork._match_1],
end

section distribution_semantics

/-- The probability of returning a given index is the independent value of getting it from both -/
lemma eval_dist_fst_map_fork_apply (i : option $ fin adv.q) :
  ⁅prod.fst <$> fork adv⁆ i = ⁅adv.simulate_choose_fork⁆ i ^ 2 :=
calc ⁅prod.fst <$> fork adv⁆ i
  = ⁅adv.simulate_choose_fork ×ₘ adv.simulate_choose_fork⁆ (i, i) : begin
    sorry
  end
  ... = ⁅adv.simulate_choose_fork⁆ i ^ 2 : begin
    rw [eval_dist_product_apply, pow_two],
  end

lemma eval_dist_fork_apply_some (i : (fin adv.q)) (x x' : α) (cache cache' : query_log (T ↦ₒ U)) :
  ⁅fork adv⁆ (some i, x, cache, x', cache') =
    ∑' (log : query_log uniform_selecting), ⁅adv.simulate_with_log⁆ (some i, x, log, cache)
      * ⁅adv.simulate_from_seed log.to_seed (cache.fork_cache () (some i))⁆ (some i, x', cache') :=
begin
  calc ⁅fork adv⁆ (some i, x, cache, x', cache')
    = ∑' (log : query_log uniform_selecting), ⁅adv.simulate_with_log⁆ (some i, x, log, cache)
        * ⁅adv.simulate_from_seed log.to_seed (cache.fork_cache () (some i))
        >>= λ o, return (ite (some i = o.fst) (some i) none, x, cache, o.snd.fst, o.snd.snd)⁆
                  (some i, x, cache, x', cache') :
    begin
      rw fork_def,
      refine (helper (λ log, (i, x, log, cache)) _ _),
      { intros o ho ho',
        simp only [support_bind_return, set.mem_image, prod.mk.inj_iff, prod.exists] at ho',
        obtain ⟨i', x'', log, ho', hi', hx', hcache, hx'', hcache'⟩ := ho',
        rw [set.mem_range],
        refine ⟨o.2.2.1, symm _⟩,
        simp only [prod.eq_iff_fst_eq_snd_eq],
        refine ⟨_, hx', rfl, hcache⟩,
        have : o.fst = i' := begin
          refine by_contra (λ hoi', option.some_ne_none i (hi'.symm.trans $ if_neg hoi')),
        end,
        refine trans (if_pos this).symm hi' },
      { simp only [],
        intros log log' h _ _,
        simp only [prod.eq_iff_fst_eq_snd_eq] at h,
        exact h.2.2.1 },
    end
    ... = ∑' (log : query_log uniform_selecting), ⁅adv.simulate_with_log⁆ (some i, x, log, cache)
      * ⁅adv.simulate_from_seed log.to_seed (cache.fork_cache () (some i))⁆ (some i, x', cache') :
    begin
      refine tsum_congr (λ log, _),
      refine congr_arg (λ x, _ * x) _,
      refine trans (eval_dist_bind_return_apply_eq_tsum_indicator _ _ _) _,
      refine trans (tsum_eq_single (some i, x', cache') _) _,
      { intros o ho,
        simp only [prod.mk.eta, set.indicator_apply_eq_zero, set.mem_preimage,
          set.mem_singleton_iff, prod.mk.inj_iff, eq_self_iff_true,
            true_and, eval_dist_eq_zero_iff_not_mem_support, and_imp],
        intros ho' ho'',
        by_cases hi : some i = o.fst,
        { exact (ho $ prod.eq_iff_fst_eq_snd_eq.2 ⟨hi.symm, ho''⟩).elim },
        { exact (option.some_ne_none i $ by rw [← ho', if_neg hi]).elim } },
      refine set.indicator_apply_eq_self.2 _,
      simp only [set.mem_preimage, eq_self_iff_true, if_true, set.mem_singleton,
        not_true, is_empty.forall_iff]
    end
end

lemma prob_fork_eq_some : ⁅λ out, out.1.is_some | fork adv⁆ ≥ (adv.advantage ^ 2) / adv.q :=
calc ⁅λ out, out.1.is_some | fork adv⁆
  = ⁅ coe ∘ option.is_some | prod.fst <$> fork adv⁆ :
    symm ((prob_event_map _ _ _))
  ... = ∑' (j : fin adv.q), (⁅prod.fst <$> fork adv⁆ (some j)) :
    (prob_event_is_some $ prod.fst <$> fork adv)
  ... = ∑' (j : fin adv.q), (⁅adv.simulate_choose_fork⁆ (some j)) ^ 2 :
    tsum_congr (λ j, eval_dist_fst_map_fork_apply _ _)
  ... = ∑ j, (⁅adv.simulate_choose_fork⁆ (some j)) ^ 2 :
    tsum_fintype _
  ... ≥ (∑ j, ⁅adv.simulate_choose_fork⁆ (some j)) ^ 2 /
          (finset.univ : finset $ fin adv.q).card ^ 1 :
    sorry --nnreal.pow_sum_div_card_le_sum_pow ⊤ (λ j, ⁅adv.simulate_choose_fork⁆ (some j)) 1
  ... ≥ (∑ j, ⁅adv.simulate_choose_fork⁆ (some j)) ^ 2 / adv.q :
    sorry --by simp only [finset.card_fin, pow_one, ge_iff_le]
  ... = (adv.advantage ^ 2) / adv.q :
    by rw forking_adversary.advantage_eq_sum adv

end distribution_semantics

section choose_fork

/-- For any non-`none` forking result, `choose_fork` matches for both side outputs -/
lemma choose_fork_eq (i : fin adv.q) (cache cache' : query_log (T ↦ₒ U)) (x x' : α)
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

lemma choose_fork_fst_eq (i : fin adv.q) (cache cache' : query_log (T ↦ₒ U)) (x x' : α)
  (h : (some i, x, cache, x', cache') ∈ (fork adv).support) :
  adv.choose_fork x cache = i :=
(choose_fork_eq adv i cache cache' x x' h).1

lemma choose_fork_snd_eq (i : fin adv.q) (cache cache' : query_log (T ↦ₒ U)) (x x' : α)
  (h : (some i, x, cache, x', cache') ∈ (fork adv).support) :
  adv.choose_fork x' cache' = i :=
(choose_fork_eq adv i cache cache' x x' h).2

lemma choose_fork_eq_choose_fork (i : fin adv.q) (cache cache' : query_log (T ↦ₒ U)) (x x' : α)
  (h : ((some i, x, cache, x', cache')) ∈ (fork adv).support) :
  adv.choose_fork x cache = adv.choose_fork x' cache' :=
by rw [choose_fork_fst_eq adv _ _ _ _ _ h, choose_fork_snd_eq adv _ _ _ _ _ h]

end choose_fork

section cache_input

/-- Because of the logging and shared cache both results of fork
  make the same query at the point specified by `choose_fork`.
  TODO: theoretically true for any `j ≤ i`, but not sure that is ever needed? -/
theorem cache_input_same_at_fork (i : fin adv.q) (cache cache' : query_log (T ↦ₒ U)) (x x' : α)
  (h : ((some i, x, cache, x', cache')) ∈ (fork adv).support) :
  query_log.query_input_same_at cache cache' () i :=
begin
  sorry
end

end cache_input

section forked_cache_differs

/- Cache values at the chosen index aren't the same. Because the cache
is forked, this only happens if both random selections are the same by pure luck. -/
def forked_cache_differs (o : option (fin n) × α × query_log (T ↦ₒ U) × α × query_log (T ↦ₒ U)) :=
query_log.query_output_diff_at o.2.2.1 o.2.2.2.2 () (option.rec_on o.1 0 coe)

section distribution_semantics

lemma prob_event_forked_cache_differs :
  ⁅forked_cache_differs | fork adv⁆ = 1 - (1 / fintype.card U) :=
sorry

lemma indep_event_forked_cache_differs_is_some :
  indep_event (fork adv) forked_cache_differs (λ o, o.1.is_some) :=
begin
  sorry
end

end distribution_semantics

end forked_cache_differs

section fork_success

/- forking algorithm succeeds if a forking point is chosen, and the query outputs differ there. -/
def fork_success (o : option (fin n) × α × query_log (T ↦ₒ U) × α × query_log (T ↦ₒ U)) :=
o.1.is_some ∧ forked_cache_differs o

/-- Probability that fork success holds is determined by adversary's initial advantage -/
theorem prob_event_fork_success : ⁅fork_success | fork adv⁆
  ≥ ((adv.advantage) ^ 2 / adv.q) - (1 / fintype.card U) :=
calc ⁅fork_success | fork adv⁆
  = ⁅λ o, o.1.is_some | fork adv⁆ * ⁅forked_cache_differs | fork adv⁆ : sorry
  ... ≥ ⁅λ o, o.1.is_some | fork adv⁆ * (1 - 1 / fintype.card U) : begin
    -- TODO: this is just an independence statement of the `is_some` and `query_output_diff_at`
    -- Slight complication in that the output diff is only well defined if a `some` index is output
    sorry
  end
  ... ≥ ⁅λ o, o.1.is_some | fork adv⁆ - (1 / fintype.card U) : begin
    sorry
  end
  ... ≥ ((adv.advantage) ^ 2 / adv.q) - (1 / fintype.card U) :
    tsub_le_tsub (prob_fork_eq_some adv) le_rfl

end fork_success