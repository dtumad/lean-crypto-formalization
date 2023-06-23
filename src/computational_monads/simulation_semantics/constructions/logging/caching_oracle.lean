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
open prod (fst) (snd)

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
{ default_state := init spec,
  o := λ i ⟨t, log⟩, match log.lookup i t with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do {u ← query i t, return (u, log.log_query i t u)}
  end }

-- TODO: Play with notation like this for convenience
@[inline, reducible, simp] def cachingₛₒ {spec : oracle_spec} := caching_oracle spec

namespace caching_oracle

variables (oa oa' : oracle_comp spec α) (i : spec.ι) (t t' : spec.domain i) (u : spec.range i)
  (log : query_log spec) (x : spec.range i × query_log spec) --TODO: naming → cache

lemma apply_eq : cachingₛₒ i (t, log) = option.rec_on (log.lookup i t)
  (query i t >>= λ u, return (u, log.log_query i t u)) (λ u, return (u, log)) :=
by {simp only [cachingₛₒ, caching_oracle, sim_oracle.has_coe_to_fun.def],
  induction log.lookup i t; refl }

lemma apply_eq_of_lookup_eq_none (hlog : log.lookup i t = none) :
  cachingₛₒ i (t, log) = (query i t >>= λ u, return (u, log.log_query i t u)) :=
by rw [apply_eq, hlog]

lemma apply_eq_of_lookup_eq_some (u : spec.range i) (hlog : log.lookup i t = some u) :
  cachingₛₒ i (t, log) = return (u, log) :=
by rw [apply_eq, hlog]

lemma apply_eq_of_not_queried (hlog : log.not_queried i t) :
  cachingₛₒ i (t, log) = (query i t >>= λ u, return (u, log.log_query i t u)) :=
by rw [apply_eq, (query_log.lookup_eq_none_iff_not_queried _ _ _).2 hlog]

@[simp] lemma apply_log_query_self :
  cachingₛₒ i (t, log.log_query i t u) = return (u, log.log_query i t u) :=
begin
  refine apply_eq_of_lookup_eq_some i t _ u _,
  rw [lookup_log_query_same_input],
end

@[simp] lemma apply_default_state :
  cachingₛₒ i (t, cachingₛₒ.default_state) =
    (query i t >>= λ u, return (u, (init _).log_query i t u)) :=
apply_eq_of_not_queried i _ _ (query_log.not_queried_init _ _)

@[simp] lemma apply_init : cachingₛₒ i (t, init spec) =
  (query i t >>= λ u, return (u, (init _).log_query i t u)) :=
apply_eq_of_not_queried i _ _ (query_log.not_queried_init _ _)

-- TODO: log query notation (maybe induction)
lemma apply_log_query_init :
  cachingₛₒ i (t', (init spec).log_query i t u) =
    if t = t' then return (u, (init spec).log_query i t u) else
      query i t' >>= λ u', return (u', ((init spec).log_query i t u).log_query i t' u') :=
begin
  split_ifs with ht,
  { rw [caching_oracle.apply_eq, lookup_log_query_init, if_pos ht] },
  { rw [caching_oracle.apply_eq, lookup_log_query_init, if_neg ht] }
end

lemma apply_log_query_init_of_index_ne {i i'} (t : spec.domain i) (t' : spec.domain i') (u')
  (hi : i' ≠ i) : cachingₛₒ i (t, (init spec).log_query i' t' u') =
    query i t >>= λ u, return (u, ((init spec).log_query i' t' u').log_query i t u) :=
begin
  refine apply_eq_of_not_queried _ _ _ _,
  refine (not_queried_log_query_of_index_ne _ hi _ _ _).2 _,
  refine (not_queried_init _ _),
end

section support

@[simp] lemma support_apply : (cachingₛₒ i (t, log)).support = if log.not_queried i t
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

lemma support_apply_of_not_queried {i t} {log : query_log spec}
  (hlog : query_log.not_queried log i t) :
  (cachingₛₒ i (t, log)).support = {x | x.2 = log.log_query i t x.1} :=
by rw [support_apply, if_pos hlog]

lemma mem_support_apply_iff_of_not_queried (hlog : log.not_queried i t) :
  x ∈ (cachingₛₒ i (t, log)).support ↔ x.2 = log.log_query i t x.1 :=
by rw [support_apply_of_not_queried hlog, set.mem_set_of_eq]

lemma support_apply_of_queried {i t} {log : query_log spec} (hlog : ¬ query_log.not_queried log i t)  :
  (cachingₛₒ i (t, log)).support = {x | some x.1 = log.lookup i t ∧ x.2 = log} :=
by rw [support_apply, if_neg hlog]

lemma mem_support_apply_iff_of_queried (hlog : ¬ log.not_queried i t) :
  x ∈ (cachingₛₒ i (t, log)).support ↔ some x.1 = log.lookup i t ∧ x.2 = log :=
by rw [support_apply_of_queried hlog, set.mem_set_of_eq]

/-- If the initial cache has `nodup` for some oracle, then so does the final cache. -/
lemma state_invariant_nodup (hlog : (log i).nodup) (x : α × query_log spec)
  (hx : x ∈ (simulate cachingₛₒ oa log).support) : (x.2 i).nodup :=
begin
  refine state_invariant_of_preserved cachingₛₒ (λ log, (log i).nodup)
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
  (hx : x ∈ (simulate cachingₛₒ oa log).support)
  (hlog : log.lookup i t = some u) : x.2.lookup i t = some u :=
begin
  refine state_invariant_of_preserved cachingₛₒ (λ log, log.lookup i t = some u)
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
  (hx : x ∈ (simulate cachingₛₒ oa log).support)
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
  (x : α × query_log spec) (hx : x ∈ (simulate cachingₛₒ oa log).support)
  (h : x.2.lookup i t = some u) (u' : spec.range i) :
  ∃ (y : α × query_log spec) (hy : y ∈ (simulate cachingₛₒ oa log).support),
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
  (x : spec.range i × query_log spec) (hx : x ∈ (cachingₛₒ i (t, log)).support) :
  (x.2 i).length = (log i).length + 1 :=
begin
  rw [support_apply_of_not_queried hlog, set.mem_set_of_eq] at hx,
  rw [hx, query_log.log_query_apply_same_index, list.length_cons],
end

lemma length_cache_apply_of_not_not_queried (hlog : ¬ log.not_queried i t)
  (x : spec.range i × query_log spec) (hx : x ∈ (cachingₛₒ i (t, log)).support) :
  (x.2 i).length = (log i).length :=
begin
  rw [mem_support_apply_iff_of_queried _ _ _ _ hlog] at hx,
  refine congr_arg list.length (congr_fun hx.2 i)
end

/-- The length of the final cache is at least as long as the initial cache. -/
lemma length_cache_le_length_cache_simulate (x : α × query_log spec)
  (hx : x ∈ (simulate cachingₛₒ oa log).support) :
  (log i).length ≤ (x.2 i).length :=
begin
  refine state_invariant_of_preserved cachingₛₒ
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
--   do {x ← cachingₛₒ i (t, log),
--     simulate' cachingₛₒ oa (f x.2)} ≃ₚ
--       simulate' cachingₛₒ oa log

open_locale classical

@[inline, reducible]
def init' {spec : oracle_spec} := init spec

notation `[` i `,` t `↦` u `]` := init'.log_query i t u

instance query_log.has_append (spec : oracle_spec) : has_append (query_log spec) :=
⟨λ log log', (λ i, log i ++ log' i)⟩

@[simp_dist_equiv] lemma fst_map_apply_bind_apply_dist_equiv
  (i : spec.ι) (t : spec.domain i) (i' : spec.ι) (t' : spec.domain i') :
  (do {x ← cachingₛₒ i' (t', init spec), fst <$> cachingₛₒ i (t, snd x)}) ≃ₚ
    fst <$> cachingₛₒ i (t, init spec) :=
calc (cachingₛₒ i' (t', init spec) >>= λ x, (fst <$> cachingₛₒ i (t, x.2))) ≃ₚ
  (query i' t' >>= λ u', return (u', [i', t' ↦ u'])) >>= λ x,
    (fst <$> cachingₛₒ i (t, x.2)) : rfl
  ... ≃ₚ (snd <$> (query i' t' >>= λ u', return (u', [i', t' ↦ u']))) >>= λ log',
    (fst <$> cachingₛₒ i (t, log')) : by pairwise_dist_equiv
  ... ≃ₚ (query i' t' >>= λ u', return [i', t' ↦ u']) >>= λ log',
    (fst <$> (cachingₛₒ i (t, log'))) : by pairwise_dist_equiv
  ... ≃ₚ query i' t' >>= λ u', (fst <$> (cachingₛₒ i (t, [i', t' ↦ u']))) :
    by pairwise_dist_equiv
  ... ≃ₚ query i t : begin
    by_cases hi : i' = i,
    { induction hi,
      by_cases ht : t' = t,
      { simp only [ht, apply_log_query_self],
        exact trans (by pairwise_dist_equiv) (bind_return_id_dist_equiv _) },
      { simp [caching_oracle.apply_log_query_init i' t' t, ht],
        exact trans (bind_dist_equiv_right _ _ default (λ x hx, by push_map_dist_equiv))
          ((fst_map_bind_return_dist_equiv _ _ _).trans (map_id_dist_equiv _)) } },
    { simp_rw [caching_oracle.apply_log_query_init_of_index_ne t t' _ hi],
      refine (bind_dist_equiv_right _ _ default (λ x hx, _)).trans (by pairwise_dist_equiv),
      apply fst_map_bind_return_dist_equiv_fst_map_bind_return }
  end
  ... ≃ₚ id <$> query i t : by pairwise_dist_equiv
  ... ≃ₚ fst <$> (query i t >>= λ u, return (u, [i, t ↦ u])) : by pairwise_dist_equiv
  ... ≃ₚ fst <$> cachingₛₒ i (t, init spec) : rfl

/-- Simulating a computation with a caching oracle to get a final cache,
throwing out some cached values, and then querying the resulting cache on a value
is distributionally equivalent to a query on its own -/
theorem simulate_bind_apply_dist_equiv_apply (oa : oracle_comp spec α)
  (i : spec.ι) (t : spec.domain i) (log : query_log spec)
  (oc : oracle_comp spec γ)
  -- (h : ∃ (oa' : oracle_comp spec α), log ∈ (snd <$> simulate cachingₛₒ oa (init spec)).support)
  -- (f : query_log spec → query_log spec) (hf : ∀ log i, f log i <+ log i)
   :
  do {x ← simulate cachingₛₒ oa (init spec), simulate' cachingₛₒ (oc ) x.2} ≃ₚ
    do {x ← simulate cachingₛₒ oa (init spec), simulate' cachingₛₒ (oc ) (init spec)} :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t' generalizing γ oc,
  { exact trans (return_bind_dist_equiv _ _) (symm (return_bind_dist_equiv _ _)) },
  {
    -- rw [simulate_bind],
    calc ((simulate cachingₛₒ oa (init spec) >>= λ x,
      simulate cachingₛₒ (ob x.1) x.2) >>= λ y,
      simulate' cachingₛₒ (oc ) y.2) ≃ₚ

    ((simulate cachingₛₒ oa (init spec) >>= λ x,
      simulate cachingₛₒ (ob x.1) (init spec)) >>= λ y,
      simulate' cachingₛₒ (oc ) y.2) : begin

        -- refine (bind_dist_equiv_bind_of_dist_equiv_left _ _ _ _),
        -- specialize hoa ob,
        sorry,
      end

    ... ≃ₚ (simulate cachingₛₒ oa (init spec) >>= λ x,
      (simulate cachingₛₒ (ob x.1) x.2) >>= λ y,
      simulate' cachingₛₒ (oc ) (y.2)) : begin
        sorry

      end

    ... ≃ₚ (simulate cachingₛₒ oa (init spec) >>= λ x,
      (simulate cachingₛₒ (ob x.1) x.2) >>= λ y,
      simulate' cachingₛₒ (oc ) (init spec)) : begin
        refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ _,
        intros x hx,
        simp only [] at hob,
        specialize hob x.1 oc,
        convert hob,
      end

    ... ≃ₚ ((simulate cachingₛₒ oa (init spec) >>= λ x,
      simulate cachingₛₒ (ob x.1) x.2) >>= λ y,
      simulate' cachingₛₒ (oc ) (init spec)) : begin
        pairwise_dist_equiv,
      end
  },
  {
    sorry,
    -- exact (fst_map_apply_bind_apply_dist_equiv i t i' t'),
    -- refl,



    -- simp_rw [simulate_query, caching_oracle.apply_init],
    -- simp [dist_equiv.ext_iff, prob_output_bind_eq_tsum,
    --   prob_output_simulate_return, prob_output_map_eq_tsum],
  }

end


section drop_at_index

--/-- Simulating a computation with a caching oracle to get a final cache,
--throwing out some cached values, and then simulating again with the partial cache
-- gives the same distribution as a single execution -/
-- theorem simulate_resimulate_dist_equiv_simulate (oa : oracle_comp spec α) (i : spec.ι) (n : ℕ) :
--   do {x ← default_simulate cachingₛₒ oa,
--     simulate cachingₛₒ oa (query_log.drop_at_index x.2 i n)} ≃ₚ
--       default_simulate cachingₛₒ oa :=
-- begin
--   -- refine bind_dist_equiv_left _ _ _,
--   -- intros x hx,
--   induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t,
--   {

--     refine bind_dist_equiv_left _ _ _,
--     intros x hx,
--     simp at hx,
--     simp [hx, simulate_return],
--     refine query_log.drop_at_index_init _ _,
--   },
--   {
--     show _ ≃ₚ simulate cachingₛₒ (oa >>= ob) (init spec),
--     rw [simulate_bind],
--     refine trans _ (bind_dist_equiv_bind_of_dist_equiv_left _ _ _ hoa),
--     sorry,
--   },
--   {

--     simp only [simulate_query, default_simulate],

--     simp only [apply_default_state],

--     refine trans (bind_map_dist_equiv _ _ _) _,

--     show (query i' t >>= (λ u, cachingₛₒ i' (t, ((init spec).log_query i' t u).drop_at_index i n))) ≃ₚ
--       query i' t >>= λ u, return (u, (init spec).log_query i' t u),

--     by_cases h : i' ≠ i ∨ n = 0,
--     { pairwise_dist_equiv,
--       cases h with hi hn,
--       { simp only [query_log.drop_at_index_log_query_of_ne _ _ _ _ hi,
--           query_log.drop_at_index_init, apply_log_query_self] },
--       { simp only [hn, drop_at_index_zero, apply_log_query_self] } },
--     { rw [not_or_distrib, not_not] at h,
--       calc (query i' t >>= (λ u, cachingₛₒ i'
--             (t, ((init spec).log_query i' t u).drop_at_index i n)))
--           ≃ₚ (query i' t >>= (λ u, cachingₛₒ i' (t, init _))) : begin
--             pairwise_dist_equiv,
--             refine congr_arg (eval_dist) _,
--             refine congr_arg (λ x, cachingₛₒ i' x) _,
--             refine prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, _⟩,
--             rw [← h.1, drop_at_index_log_query_init_eq_init _ _ _ h.2],
--           end
--           ... ≃ₚ cachingₛₒ i' (t, init _) : by pairwise_dist_equiv
--           ... ≃ₚ query i' t >>= λ u, return (u, (init spec).log_query i' t u) :
--             by rw [apply_init] } }
-- end

end drop_at_index

section fork

/-- Given a `query_log`, and a output of simulating with that as the cache,
simulation with the `fork_cache` applied to the new cache has the same support as simulating
with the original cache. Intuitively, since all the new entries to the cache just come
from a call to `query`, it's irrelevent that they have been added, since any new call
can't tell whether this call to `query` is new or made earlier. -/
theorem support_simulate_fork_cache_some
  (cache : query_log spec) (i : spec.ι) (n : ℕ) (hn : (cache i).length ≤ n)
  (x : α × query_log spec) (hx : x ∈ (simulate cachingₛₒ oa' cache).support) :
  (simulate cachingₛₒ oa (x.2.fork_cache i (some n))).support =
    (simulate cachingₛₒ oa cache).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  sorry, sorry, sorry,
end

/-- Specialized version of `support_simulate_fork_cache_some` when the initial state is empty.
In this case we don't need to place any restrictions on the value of `n`-/
lemma support_simulate_init_fork_cache_some (i : spec.ι) (n : ℕ) (x : α × query_log spec)
  (hx : x ∈ (simulate cachingₛₒ oa' (init spec)).support) :
  (simulate cachingₛₒ oa (x.2.fork_cache i (some n))).support =
    (simulate cachingₛₒ oa (init spec)).support :=
begin
  sorry,
end

/-- Version of `support_simulate_fork_cache` for forking on `none` -/
lemma support_simulate_fork_cache_none (i : spec.ι) (cache : query_log spec) :
  (simulate cachingₛₒ oa (cache.fork_cache i none)).support =
    (simulate cachingₛₒ oa (init spec)).support :=
by rw query_log.fork_cache_none

end fork


-- TODO: generalize. Should also work for log→seed probably ?
/-- Re-running a computation with an old cache doesn't change the possible outputs,
assuming the old cache was generated by an honest simulation. -/
theorem support_simulate_bind_simulate_eq_support_simulate (oa : oracle_comp spec α) :
  (simulate cachingₛₒ oa log >>= λ x, simulate cachingₛₒ oa x.2).support =
    (simulate cachingₛₒ oa log).support :=
begin
  -- apply support_bind_eq_support,
  refine support_simulate_simulate_eq_support_simulate cachingₛₒ cachingₛₒ
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