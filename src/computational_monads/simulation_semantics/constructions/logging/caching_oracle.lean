/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.query_log.lookup
import computational_monads.simulation_semantics.constructions.logging.query_log.fork
import computational_monads.simulation_semantics.oracle_compose
import computational_monads.distribution_semantics.tactics.push_map_dist_equiv

/-!
# Caching Simulation Oracle

This file defines a `sim_oracle` that implements caching functionality.
`caching_oracle` represents a simulator that logs all new queries, returning the old
log values for queries that have been previously asked, so the `query_log` functions as a cache.
This is often useful when composed with other oracles, such as in `random_oracle`.
-/

open oracle_comp oracle_spec query_log

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Computation that returns a currently cached value, or queries a new value if needed,
returning both the result and the (potentially updated) cache.
The function for a fresh query is given by `ou`, which may have other oracles than the cache.
-- TODO: use this? -/
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

lemma apply_eq : (caching_oracle spec) i (t, log) = option.rec_on (log.lookup i t)
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

lemma apply_log_query_self :
  (caching_oracle spec) i (t, log.log_query i t u) = return (u, log.log_query i t u) :=
begin
  refine apply_eq_of_lookup_eq_some i t _ u _,
  rw [lookup_log_query_same_input],
end

@[simp] lemma apply_default_state :
  (caching_oracle spec) i (t, (caching_oracle spec).default_state) =
    (query i t >>= λ u, return (u, (query_log.init _).log_query i t u)) :=
apply_eq_of_not_queried i _ _ (query_log.not_queried_init _ _)

@[simp] lemma apply_init : (caching_oracle spec) i (t, query_log.init spec) =
  (query i t >>= λ u, return (u, (query_log.init _).log_query i t u)) :=
apply_eq_of_not_queried i _ _ (query_log.not_queried_init _ _)

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

lemma support_apply_of_not_queried {i t log} (hlog : query_log.not_queried log i t) :
  ((caching_oracle spec) i (t, log)).support = {x | x.2 = log.log_query i t x.1} :=
by rw [support_apply, if_pos hlog]

lemma mem_support_apply_iff_of_not_queried (hlog : log.not_queried i t) :
  x ∈ ((caching_oracle spec) i (t, log)).support ↔ x.2 = log.log_query i t x.1 :=
by rw [support_apply_of_not_queried hlog, set.mem_set_of_eq]

lemma support_apply_of_queried {i t log} (hlog : ¬ query_log.not_queried log i t)  :
  ((caching_oracle spec) i (t, log)).support = {x | some x.1 = log.lookup i t ∧ x.2 = log} :=
by rw [support_apply, if_neg hlog]

lemma mem_support_apply_iff_of_queried (hlog : ¬ log.not_queried i t) :
  x ∈ ((caching_oracle spec) i (t, log)).support ↔ some x.1 = log.lookup i t ∧ x.2 = log :=
by rw [support_apply_of_queried hlog, set.mem_set_of_eq]

/-- If the initial cache has `nodup` for some oracle, then so does the final cache. -/
lemma state_invariant_nodup (hlog : (log i).nodup) (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support) : (x.2 i).nodup :=
begin
  refine state_invariant_of_preserved (caching_oracle spec) (λ log, (log i).nodup)
    (λ i t log x hx hlog, _) log hlog oa x hx,
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
  refine state_invariant_of_preserved (caching_oracle spec) (λ log, log.lookup i t = some u)
    (λ i t log x hx hlog, _) log hlog oa x hx,
  by_cases h : log.not_queried i t,
  { rw [support_apply_of_not_queried h, set.mem_set_of_eq] at hx,
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
  rw [support_apply_of_not_queried hlog, set.mem_set_of_eq] at hx,
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
  refine state_invariant_of_preserved (caching_oracle spec)
    (λ log', (log i).length ≤ (log' i).length) (λ i' t log' x' hx' hlog', le_trans hlog' _)
      log le_rfl oa x hx ,
  by_cases hlog'' : log'.not_queried i' t,
  { rw [support_apply_of_not_queried hlog''] at hx',
    exact hx'.symm ▸ log'.length_apply_le_lenght_log_query_apply i' t x'.1 i },
  { rw [mem_support_apply_iff_of_queried _ _ _ _ hlog''] at hx',
    rw [hx'.2] }
end

end length

def query_log.sublog (log log' : query_log spec) := ∀ i, log i <+ log' i

infix ` <++ `:50 := query_log.sublog

lemma sublog_init_iff {log : query_log spec} : log <++ init spec ↔ log = init spec :=
begin
  sorry,
end

-- lemma caching_oracle_general (log : query_log spec) (i : spec.ι) (t : spec.domain i)
--   (f : query_log spec → query_log spec) (hf : ∀ log, f log <++ log) :
--   do {x ← (caching_oracle spec) i (t, log),
--     simulate' (caching_oracle spec) oa (f x.2)} ≃ₚ
--       simulate' (caching_oracle spec) oa log

theorem most_general''_wo_f (oa : oracle_comp spec α) (oc : α → oracle_comp spec γ) :
  do {x ← simulate (caching_oracle spec) oa (init spec),
    simulate' (caching_oracle spec) (oc x.1) (x.2)} ≃ₚ
    do {x ← simulate' (caching_oracle spec) oa (init spec),
      simulate' (caching_oracle spec) (oc x) (init spec)} :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t generalizing γ oc,
  { simp [simulate_return],

    refine trans (return_bind_dist_equiv _ _) _,

    refine trans (return_bind_dist_equiv a _).symm _,
    refine bind_dist_equiv_bind_of_dist_equiv _ _,
    pairwise_dist_equiv,
    simp },
  {
    simp only [] at hoa hob,
    rw [simulate_bind],
    specialize hoa ob,
  }

end

theorem most_general'' (oa : oracle_comp spec α) (oc : α → oracle_comp spec γ)
  (f : query_log spec → query_log spec) (hf : ∀ log', f log' <++ log') :
  do {x ← simulate (caching_oracle spec) oa (init spec),
    simulate' (caching_oracle spec) (oc x.1) (f x.2)} ≃ₚ
    do {x ← simulate' (caching_oracle spec) oa (init spec),
      simulate' (caching_oracle spec) (oc x) (init spec)} :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t generalizing γ oc,
  { simp [simulate_return],

    refine trans (return_bind_dist_equiv _ _) _,

    refine trans (return_bind_dist_equiv a _).symm _,
    refine bind_dist_equiv_bind_of_dist_equiv _ _,
    pairwise_dist_equiv,
    sorry },
  {
    simp only [] at hoa hob,
    rw [simulate_bind],
    specialize hoa ob,
  }

end

theorem most_general' (oa : oracle_comp spec α) (oa' : oracle_comp spec γ)
  (f : query_log spec → query_log spec) (hf : ∀ log', f log' <++ log') :
  do {x ← simulate (caching_oracle spec) oa (init spec),
    simulate' (caching_oracle spec) oa' (f x.2)} ≃ₚ
      simulate' (caching_oracle spec) oa' (init spec) :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t generalizing oa',
  { simp [simulate_return],

    refine trans (return_bind_dist_equiv _ _) _,
    refine dist_equiv_of_eq _,
    refine congr_arg (simulate' (caching_oracle _) oa') _,
    refine sublog_init_iff.1 (hf (init _)),
     },
  {
    simp only [] at hoa hob,
    rw [simulate_bind],
  }

end

theorem most_general (oa : oracle_comp spec α) (log : query_log spec)
  (f : query_log spec → query_log spec) (hf : ∀ log, f log <++ log)
  (hlog : ∀ log' ∈ (prod.snd <$> simulate (caching_oracle spec) oa log).support, log <++ f log') :
  do {x ← simulate (caching_oracle spec) oa log,
    simulate' (caching_oracle spec) oa (f x.2)} ≃ₚ
      simulate' (caching_oracle spec) oa log :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t generalizing log,
  { refine trans (return_bind_dist_equiv _ _) (fst_map_return_dist_equiv_fst_map_return _ _ _) },
  {
    simp at hoa hob,
    specialize hoa log,
    calc ((simulate (caching_oracle spec) (oa >>= ob) log) >>=
        λ x, simulate' (caching_oracle spec) (oa >>= ob) (f x.2)) ≃ₚ
        ((simulate (caching_oracle spec) (oa >>= ob) log) >>=
          λ x, simulate' (caching_oracle spec) (oa >>= ob) (f x.2)) :
      begin
        refl,
      end
      ... ≃ₚ ((simulate (caching_oracle spec) (oa) log) >>=
        λ x, simulate' (caching_oracle spec) (ob x.1) (x.2)) : begin

        simp only [simulate_bind],
      end
      ... ≃ₚ simulate' (caching_oracle spec) (oa >>= ob) log : by pairwise_dist_equiv
  },
  {
    sorry
  }
end

-- theorem most_general_with_init (oa : oracle_comp spec α)
--   (f : query_log spec → query_log spec) (hf : ∀ log, f log <++ log) :
--   do {x ← simulate (caching_oracle spec) oa (init spec),
--     simulate (caching_oracle spec) oa (f x.2)} ≃ₚ
--       simulate (caching_oracle spec) oa (init spec) :=
-- begin
--   induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t,
--   {
--     simp only [simulate_return],
--     refine bind_dist_equiv_left _ _ _,
--     intros x hx,
--     simp at hx,
--     simp [hx, simulate_return, ← sublog_init_iff, hf],
--   },
--   {
--     simp only [] at hoa hob,
--   }
-- end

section drop_at_index

/-- Simulating a computation with a caching oracle to get a final cache,
throwing out some cached values, and then simulating again with the partial cache
gives the same distribution as a single execution -/
theorem simulate_resimulate_dist_equiv_simulate (oa : oracle_comp spec α) (i : spec.ι) (n : ℕ) :
  do {x ← default_simulate (caching_oracle spec) oa,
    simulate (caching_oracle spec) oa (query_log.drop_at_index x.2 i n)} ≃ₚ
      default_simulate (caching_oracle spec) oa :=
begin
  -- refine bind_dist_equiv_left _ _ _,
  -- intros x hx,
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t,
  {

    refine bind_dist_equiv_left _ _ _,
    intros x hx,
    simp at hx,
    simp [hx, simulate_return],
    refine query_log.drop_at_index_init _ _,
  },
  {
    show _ ≃ₚ simulate (caching_oracle spec) (oa >>= ob) (init spec),
    rw [simulate_bind],
    refine trans _ (bind_dist_equiv_bind_of_dist_equiv_left _ _ _ hoa),
    sorry,
  },
  {

    simp only [simulate_query, default_simulate],

    simp only [apply_default_state],

    refine trans (bind_map_dist_equiv _ _ _) _,

    show (query i' t >>= (λ u, (caching_oracle spec) i' (t, ((query_log.init spec).log_query i' t u).drop_at_index i n))) ≃ₚ
      query i' t >>= λ u, return (u, (query_log.init spec).log_query i' t u),

    by_cases h : i' ≠ i ∨ n = 0,
    { pairwise_dist_equiv,
      cases h with hi hn,
      { simp only [query_log.drop_at_index_log_query_of_ne _ _ _ _ hi,
          query_log.drop_at_index_init, apply_log_query_self] },
      { simp only [hn, drop_at_index_zero, apply_log_query_self] } },
    { rw [not_or_distrib, not_not] at h,
      calc (query i' t >>= (λ u, (caching_oracle spec) i'
            (t, ((query_log.init spec).log_query i' t u).drop_at_index i n)))
          ≃ₚ (query i' t >>= (λ u, (caching_oracle spec) i' (t, query_log.init _))) : begin
            pairwise_dist_equiv,
            refine congr_arg (eval_dist) _,
            refine congr_arg (λ x, (caching_oracle spec) i' x) _,
            refine prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, _⟩,
            rw [← h.1, drop_at_index_log_query_init_eq_init _ _ _ h.2],
          end
          ... ≃ₚ (caching_oracle spec) i' (t, query_log.init _) : by pairwise_dist_equiv
          ... ≃ₚ query i' t >>= λ u, return (u, (query_log.init spec).log_query i' t u) :
            by rw [apply_init] } }
end

end drop_at_index

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
  -- apply support_bind_eq_support,
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