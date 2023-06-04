/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.query_log.lookup
import computational_monads.simulation_semantics.constructions.logging.query_log.fork
import computational_monads.simulation_semantics.oracle_compose

/-!
# Caching Simulation Oracle

This file defines a `sim_oracle` that implements caching functionality.
`caching_oracle` represents a simulator that logs all new queries, returning the old
log values for queries that have been previously asked, so the `query_log` functions as a cache.
This is often useful when composed with other oracles, such as in `random_oracle`.
-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Computation that returns a currently cached value, or queries a new value if needed,
returning both the result and the (potentially updated) cache.
The function for a fresh query is given by `ou`, which may have other oracles than the cache. -/
def query_log.lookup_cached_or_run
  (cache : query_log spec) (i : spec.ι) (t : spec.domain i)
  (ou : oracle_comp spec' (spec.range i)) :
  oracle_comp spec' (spec.range i × query_log spec) :=
match cache.lookup i t with
| (some u) := return (u, cache)
| none := do {u ← ou, return (u, cache.log_query i t u)}
end

/-- Oracle for logging previous queries, and returning the same value for matching inputs -/
def caching_oracle (spec : oracle_spec) : sim_oracle spec spec (query_log spec) :=
{ default_state := query_log.init spec,
  o := λ i ⟨t, log⟩, match log.lookup i t with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do {u ← query i t, return (u, log.log_query i t u)}
  end }

namespace caching_oracle

variables (oa oa' : oracle_comp spec α) (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (log : query_log spec) (x : spec.range i × query_log spec) --TODO: naming → cache

@[simp] lemma apply_eq : (caching_oracle spec) i (t, log) = option.rec_on (log.lookup i t)
  (query i t >>= λ u, return (u, log.log_query i t u)) (λ u, return (u, log)) :=
by {simp only [caching_oracle, sim_oracle.has_coe_to_fun.def], induction log.lookup i t; refl }

lemma apply_eq_of_lookup_eq_none (hlog : log.lookup i t = none) :
  (caching_oracle spec) i (t, log) = (query i t >>= λ u, return (u, log.log_query i t u)) :=
by rw [apply_eq, hlog]

lemma apply_eq_of_lookup_eq_some (u : spec.range i) (hlog : log.lookup i t = some u) :
  (caching_oracle spec) i (t, log) = return (u, log) :=
by rw [apply_eq, hlog]

lemma apply_eq_of_not_queried (hlog : log.not_queried i t) :
  (caching_oracle spec) i (t, log) = (query i t >>= λ u, return (u, log.log_query i t u)) :=
by rw [apply_eq, (query_log.lookup_eq_none_iff_not_queried _ _ _).2 hlog]

section support

@[simp] lemma support_apply : ((caching_oracle spec) i (t, log)).support = if log.not_queried i t
  then {x | x.2 = log.log_query i t x.1} else {x | some x.1 = log.lookup i t ∧ x.2 = log} :=
begin
  split_ifs with hlog; ext x,
  { rw [apply_eq_of_not_queried i t log hlog, support_bind_return, support_query,
      set.image_univ, set.mem_range, set.mem_set_of_eq],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨u, rfl⟩ := h,
      refl },
    { exact ⟨x.1, h ▸ (prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, rfl⟩)⟩ } },
  { obtain ⟨u, hu⟩ := log.exists_eq_lookup_of_not_not_queried i t hlog,
    simp only [apply_eq_of_lookup_eq_some _ _ _ u hu.symm, ← hu, support_return,
      prod.eq_iff_fst_eq_snd_eq, set.mem_singleton_iff, set.mem_set_of_eq] }
end

lemma support_apply_of_not_queried (hlog : log.not_queried i t) :
  ((caching_oracle spec) i (t, log)).support = {x | x.2 = log.log_query i t x.1} :=
by rw [support_apply, if_pos hlog]

lemma mem_support_apply_iff_of_not_queried (hlog : log.not_queried i t) :
  x ∈ ((caching_oracle spec) i (t, log)).support ↔ x.2 = log.log_query i t x.1 :=
by rw [support_apply_of_not_queried i t log hlog, set.mem_set_of_eq]

lemma support_apply_of_queried (hlog : ¬ log.not_queried i t) :
  ((caching_oracle spec) i (t, log)).support = {x | some x.1 = log.lookup i t ∧ x.2 = log} :=
by rw [support_apply, if_neg hlog]

lemma mem_support_apply_iff_of_queried (hlog : ¬ log.not_queried i t) :
  x ∈ ((caching_oracle spec) i (t, log)).support ↔ some x.1 = log.lookup i t ∧ x.2 = log :=
by rw [support_apply_of_queried i t log hlog, set.mem_set_of_eq]

/-- If the initial cache has `nodup` for some oracle, then so does the final cache. -/
lemma nodup_simulate (hlog : (log i).nodup) (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support) : (x.2 i).nodup :=
begin
  refine support_state_simulate_induction (caching_oracle spec) (λ log, (log i).nodup)
    log hlog oa x hx (λ i t log x hx hlog, _),
  by_cases h : log.not_queried i t,
  { rw [mem_support_apply_iff_of_not_queried _ _ _ _ h] at hx,
    rw [hx, query_log.nodup_log_query_apply_iff _ _ _ _ _ hlog],
    exact or.inr ((log.not_queried_iff_not_mem _ _).1 h _) },
  { rw [mem_support_apply_iff_of_queried _ _ _ _ h] at hx,
    exact hx.2.symm ▸ hlog }
end

section lookup

/-- If a value is already cached in the initial state, it has the same cache value after. -/
lemma lookup_simulate_eq_some_of_lookup_eq_some (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support)
  (hlog : log.lookup i t = some u) : x.2.lookup i t = some u :=
begin
  refine support_state_simulate_induction (caching_oracle spec) (λ log, log.lookup i t = some u)
    log hlog oa x hx (λ i t log x hx hlog, _),
  by_cases h : log.not_queried i t,
  { rw [support_apply_of_not_queried _ _ _ h, set.mem_set_of_eq] at hx,
    rw [hx, query_log.lookup_log_query],
    split_ifs with hi ht,
    { obtain rfl := ht,
      obtain rfl := hi,
      exact false.elim (option.some_ne_none u (trans hlog.symm $
        (log.lookup_eq_none_iff_not_queried _ _).2 h)) },
    { exact hlog },
    { exact hlog } },
  { rw [mem_support_apply_iff_of_queried _ _ _ _ h] at hx,
    exact hx.2.symm ▸ hlog }
end

/-- If a value isn't cached after simulation, it wasn't cached in the initial state. -/
lemma lookup_eq_none_of_lookup_simulate_eq_none (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support)
  (hx' : x.2.lookup i t = none) : log.lookup i t = none :=
begin
  by_contradiction h,
  rw [← ne.def, option.ne_none_iff_exists'] at h,
  refine let ⟨u, hu⟩ := h in option.some_ne_none u ((lookup_simulate_eq_some_of_lookup_eq_some
    oa i t u log x hx hu).symm.trans hx'),
end

/-- For any query fresh to the initial cache, if there is some output such that query has a cached
value, then there are also outputs with any other possible cached value. -/
lemma exists_cache_lookup_eq_some (hlog : log.not_queried i t)
  (x : α × query_log spec) (hx : x ∈ (simulate (caching_oracle spec) oa log).support)
  (h : x.2.lookup i t = some u) (u' : spec.range i) :
  ∃ (y : α × query_log spec) (hy : y ∈ (simulate (caching_oracle spec) oa log).support),
    y.2.lookup i t = some u' :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { rw [support_simulate_return, set.mem_singleton_iff] at hx,
    have : ¬ log.not_queried i t := begin
      rw [← query_log.lookup_eq_none_iff_not_queried,
        option.eq_none_iff_forall_not_mem, not_forall],
      refine ⟨u, _⟩,
      simpa only [hx] using h,
    end,
    refine (this hlog).elim },
  sorry, sorry,
end

end lookup

section length

lemma length_cache_apply_of_not_queried (hlog : log.not_queried i t)
  (x : spec.range i × query_log spec) (hx : x ∈ ((caching_oracle spec) i (t, log)).support) :
  (x.2 i).length = (log i).length + 1 :=
begin
  rw [support_apply_of_not_queried i t log hlog, set.mem_set_of_eq] at hx,
  rw [hx, query_log.log_query_apply_same_index, list.length_cons],
end

lemma length_cache_apply_of_not_not_queried (hlog : ¬ log.not_queried i t)
  (x : spec.range i × query_log spec) (hx : x ∈ ((caching_oracle spec) i (t, log)).support) :
  (x.2 i).length = (log i).length :=
begin
  rw [mem_support_apply_iff_of_queried _ _ _ _ hlog] at hx,
  refine congr_arg list.length (congr_fun hx.2 i)
end

/-- The length of the final cache is at least as long as the initial cache. -/
lemma length_cache_le_length_cache_simulate (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support) :
  (log i).length ≤ (x.2 i).length :=
begin
  refine support_state_simulate_induction (caching_oracle spec)
    (λ log', (log i).length ≤ (log' i).length) log le_rfl oa
      x hx (λ i' t log' x' hx' hlog', le_trans hlog' _),
  by_cases hlog'' : log'.not_queried i' t,
  { rw [support_apply_of_not_queried _ _ _ hlog''] at hx',
    exact hx'.symm ▸ log'.length_apply_le_lenght_log_query_apply i' t x'.1 i },
  { rw [mem_support_apply_iff_of_queried _ _ _ _ hlog''] at hx',
    rw [hx'.2] }
end

end length

section fork

/-- Given a `query_log`, and a output of simulating with that as the cache,
simulation with the `fork_cache` applied to the new cache has the same support as simulating
with the original cache. Intuitively, since all the new entries to the cache just come
from a call to `query`, it's irrelevent that they have been added, since any new call
can't tell whether this call to `query` is new or made earlier. -/
theorem support_simulate_fork_cache_some
  (cache : query_log spec) (i : spec.ι) (n : ℕ) (hn : (cache i).length ≤ n)
  (x : α × query_log spec) (hx : x ∈ (simulate (caching_oracle spec) oa' cache).support) :
  (simulate (caching_oracle spec) oa (x.2.fork_cache i (some n))).support =
    (simulate (caching_oracle spec) oa cache).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  sorry, sorry, sorry,
end

/-- Specialized version of `support_simulate_fork_cache_some` when the initial state is empty.
In this case we don't need to place any restrictions on the value of `n`-/
lemma support_simulate_init_fork_cache_some (i : spec.ι) (n : ℕ) (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa' (query_log.init spec)).support) :
  (simulate (caching_oracle spec) oa (x.2.fork_cache i (some n))).support =
    (simulate (caching_oracle spec) oa (query_log.init spec)).support :=
begin
  sorry,
end

/-- Version of `support_simulate_fork_cache` for forking on `none` -/
lemma support_simulate_fork_cache_none (i : spec.ι) (cache : query_log spec) :
  (simulate (caching_oracle spec) oa (cache.fork_cache i none)).support =
    (simulate (caching_oracle spec) oa (query_log.init spec)).support :=
by rw query_log.fork_cache_none

end fork

-- TODO: generalize. Should also work for log→seed probably ?
/-- Re-running a computation with an old cache doesn't change the possible outputs,
assuming the old cache was generated by an honest simulation. -/
theorem support_simulate_bind_simulate_eq_support_simulate (oa : oracle_comp spec α) :
  (simulate (caching_oracle spec) oa log >>= λ x, simulate (caching_oracle spec) oa x.2).support =
    (simulate (caching_oracle spec) oa log).support :=
begin
  refine support_simulate_simulate_eq_support_simulate (caching_oracle spec) (caching_oracle spec)
    _ log oa,
  clear log,
  intros i t log,
  ext x,
  refine ⟨λ h, _, λ h, _⟩,
  { simp_rw [set.mem_Union] at h,
    obtain ⟨y, hy, hy'⟩ := h,
    by_cases hlog : log.not_queried i t,
    { rw [mem_support_apply_iff_of_not_queried _ _ _ _ hlog] at ⊢ hy,
      have : ¬ y.2.not_queried i t := sorry,
      rw [mem_support_apply_iff_of_queried _ _ _ _ this] at hy',
      refine hy'.2.trans _,
      have : x.1 = y.1 := sorry,
      rw [hy, this] },
    { rw [mem_support_apply_iff_of_queried _ _ _ _ hlog] at ⊢ hy,
      have : ¬ y.2.not_queried i t := sorry,
      rw [mem_support_apply_iff_of_queried _ _ _ _ this] at hy',
      refine ⟨trans (hy'.1.trans _) hy.1, hy'.2.trans hy.2⟩,
      rw [hy.2],
      exact symm hy.1 } },
  sorry,
end

end support

section eval_dist


end eval_dist

end caching_oracle