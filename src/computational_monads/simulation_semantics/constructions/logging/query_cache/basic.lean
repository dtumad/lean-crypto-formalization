/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec

/-!
# Oracle Query Cache

This file defines a cache for storing oracle queries and recalling cached values.
We construct them as functions from oracle indices and inputs to optional output values.
This automatically gives order independence of cache values and uniqeness of cache values.
Updates are done using continuation passing with the previous cache.
-/

/-- Data type representing a log of oracle queries for a given `oracle_spec`.
  Represented as a list of query inputs and outputs, indexed by the indexing set in the spec -/
def query_cache (spec : oracle_spec) : Type :=
Π (i : spec.ι), spec.domain i → option (spec.range i)

namespace query_cache

open oracle_spec

variables {spec : oracle_spec} (cache cache' : query_cache spec)

@[ext] protected lemma ext {spec : oracle_spec} {log log' : query_cache spec}
  (h : ∀ (i : spec.ι) t, log i t = log' i t) : log = log' := funext (λ _, funext (λ _, h _ _))

protected lemma ext_iff {spec : oracle_spec} {log log' : query_cache spec} :
  log = log' ↔ ∀ (i : spec.ι) t, log i t = log' i t :=
⟨λ h i t, h ▸ rfl, query_cache.ext⟩

section lookup

variables (i : spec.ι) (t : spec.domain i)

def lookup (cache : query_cache spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) := cache i t

lemma lookup_ne_none_iff_exists_eq_some :
  cache.lookup i t ≠ none ↔ ∃ u, cache.lookup i t = some u := sorry

end lookup

section is_fresh

variables (i : spec.ι) (t : spec.domain i)

def is_fresh (i : spec.ι) (t : spec.domain i) := (cache.lookup i t).is_none = tt

@[simp] lemma lookup_eq_none_iff_is_fresh : cache.lookup i t = none ↔ cache.is_fresh i t :=
by simp [is_fresh, option.is_none_iff_eq_none]

lemma is_fresh_of_lookup_eq_none {i t} (h : cache.lookup i t = none) : cache.is_fresh i t :=
(lookup_eq_none_iff_is_fresh cache i t).1 h

lemma not_is_fresh_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  ¬ cache.is_fresh i t := by simp [is_fresh, h]

end is_fresh

section is_cached

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

def is_cached (i : spec.ι) (t : spec.domain i) := (cache.lookup i t).is_some = tt

lemma is_cached_iff_exists_lookup_eq_some :
  cache.is_cached i t ↔ ∃ u, cache.lookup i t = some u :=
by simp [is_cached, ← option.is_some_iff_exists]

lemma is_cached_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  cache.is_cached i t := (is_cached_iff_exists_lookup_eq_some cache i t).2 ⟨u, h⟩

lemma not_is_cached_of_lookup_eq_none {i t} (h : cache.lookup i t = none) :
  ¬ cache.is_cached i t := by simp [is_cached, h]

lemma is_cached_iff_not_is_fresh : cache.is_cached i t ↔ ¬ cache.is_fresh i t :=
by {simp [is_cached, is_fresh], cases cache.lookup i t; simp}

end is_cached


section init

variables (i : spec.ι) (t : spec.domain i)

@[inline, reducible] protected def init (spec : oracle_spec) :
  query_cache spec := λ _ _, none

instance : has_emptyc (query_cache spec) := ⟨query_cache.init spec⟩

lemma init_apply' : (∅ : query_cache spec) i = λ _, none := rfl

lemma init_apply : (∅ : query_cache spec) i t = none := rfl

@[simp] lemma lookup_init : lookup ∅ i t = none := rfl

lemma lookup_init_ne_some (u : spec.range i) : lookup ∅ i t ≠ some u := by simp

@[simp] lemma is_fresh_init : is_fresh ∅ i t := by simp [is_fresh]

@[simp] lemma not_is_cached_init : ¬ is_cached ∅ i t := by simp [is_cached]

end init

section order -- TODO: `is_mono` typeclass for `sim_oracle`.

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

/-- We say `cache ≤ cache'` for two query caches it every cached value in `cache` has the same
value cached in `cache'`. For uncached values the corresponding value can be anything. -/
instance : partial_order (query_cache spec) :=
{ le := λ cache cache', ∀ i t u, cache.lookup i t = some u → cache'.lookup i t = some u,
  le_refl := λ cache i t u h, h,
  le_trans := λ cache cache' cache'' h h' i t u h'', h' i t u (h i t u h''),
  le_antisymm := λ cache cache' h' h, query_cache.ext (λ i t,
    begin
      by_cases hi : cache i t = none,
      { by_cases hi' : cache' i t = none,
        { rw [hi, hi'] },
        { obtain ⟨u, hu⟩ := option.ne_none_iff_exists'.1 hi',
          refine (option.some_ne_none u ((h i t u hu).symm.trans hi)).elim } },
      { exact let ⟨u, hu⟩ := option.ne_none_iff_exists'.1 hi in (hu.trans (h' i t u hu).symm) }
    end) }

lemma le_iff : cache ≤ cache' ↔ ∀ i t u, cache.lookup i t = some u → cache'.lookup i t = some u :=
iff.rfl

lemma lt_iff_le_and_exists : cache < cache' ↔ cache ≤ cache' ∧
  ∃ i t, (cache.lookup i t).is_none ∧ (cache'.lookup i t).is_some :=
begin
  sorry
end

/-- The "smallest" element in the `query_cache` ordering is the empty cache. -/
instance : order_bot (query_cache spec) :=
{ bot := ∅,
  bot_le := λ cache i t u h, (lookup_init_ne_some i t u h).elim }

lemma bot_eq_init (spec : oracle_spec) : (⊥ : query_cache spec) = ∅ := rfl

@[simp] lemma le_init : ∅ ≤ cache := bot_le

@[simp] lemma lt_init_iff : ∅ < cache ↔ cache ≠ ∅ := bot_lt_iff_ne_bot

@[simp] lemma init_le_iff : cache ≤ ∅ ↔ cache = ∅ := le_bot_iff

@[simp] lemma not_init_lt : ¬ cache < ∅ := not_lt_bot

lemma lookup_eq_some_of_le (h : cache ≤ cache')
  (h' : cache.lookup i t = some u) : cache'.lookup i t = some u :=
h i t u h'

lemma lookup_eq_none_of_le (h : cache ≤ cache')
  (h' : cache'.lookup i t = none) : cache.lookup i t = none :=
by_contra (λ hs, let ⟨u, hu⟩ := (lookup_ne_none_iff_exists_eq_some _ _ _).1 hs in
  (option.some_ne_none u ((h i t u hu).symm.trans h')))

end order

section cache_query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

def cache_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) (cache : query_cache spec) :
  query_cache spec := λ i' t', if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t'

notation `[` i `,` t `↦` u `;` cache `]` := cache_query i t u cache

notation `[` i `,` t `↦` u `]` := cache_query i t u ∅

@[simp] lemma lookup_cache_query (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t' := rfl

lemma lookup_singleton (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else none) else none := rfl

lemma lookup_cache_query_same_index (t' : spec.domain i) :
  [i, t ↦ u; cache].lookup i t' = if t = t' then some u else cache.lookup i t' := by simp

lemma lookup_singleton_same_index (t' : spec.domain i) :
  [i, t ↦ u].lookup i t' = if t = t' then some u else none := by simp

lemma lookup_cache_query_same_input : [i, t ↦ u; cache].lookup i t = some u := by simp

lemma lookup_singleton_same_input : [i, t ↦ u].lookup i t = some u := by simp

@[simp] lemma is_fresh_cache_query_iff (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache].is_fresh i' t' ↔ cache.is_fresh i' t' ∧
    (if h : i = i' then h.rec t ≠ t' else true) :=
begin
  simp only [← lookup_eq_none_iff_is_fresh, lookup_cache_query],
  split_ifs with hi ht,
  { induction hi, induction ht, simp },
  { induction hi, simp [ht] },
  { simp }
end

@[simp] lemma is_cached_cache_query_iff (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache].is_cached i' t' ↔ cache.is_cached i' t' ∨
    (if h : i = i' then h.rec t = t' else false) :=
begin
  simp only [is_cached_iff_not_is_fresh, is_fresh_cache_query_iff, not_and_distrib],
  split_ifs with hi; simp,
end

section order

lemma cache_query_monotone : monotone (cache_query i t u) :=
λ cache cache' h i' t' u', by {simp only [lookup_cache_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

lemma le_cache_query_iff_of_is_fresh (h : cache'.is_fresh i t) :
  cache ≤ [i, t ↦ u; cache'] ↔ (cache.is_fresh i t ∨ cache.lookup i t = some u) ∧ cache ≤ cache' :=
begin
  sorry
end

-- lemma lt_cache_query_iff_of_is_fresh (h : cache.is_fresh i t) :
--   cache < [i, t ↦ u; cache'] ↔ cache < cache' :=
-- begin
--   sorry
-- end

-- lemma cache_query_le_iff_of_is_fresh (h : cache.is_fresh i t) :
--   [i, t ↦ u; cache] ≤ cache' ↔ cache'.lookup i t = some u ∧ cache ≤ cache' :=
-- begin
--   sorry
-- end

-- lemma cache_query_lt_iff_of_is_fresh (h : cache.is_fresh i t) :
--   [i, t ↦ u; cache] < cache' ↔ cache'.lookup i t = some u ∧ cache < cache' :=
-- begin
--   sorry
-- end

-- lemma le_cache_query_iff_of_is_cached (h : cache.is_cached i t) :
--   cache ≤ [i, t ↦ u; cache'] ↔


end order

end cache_query

section drop_query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

def drop_query (i : spec.ι) (t : spec.domain i) (cache : query_cache spec) :
  query_cache spec := λ i' t', if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t'

@[simp] lemma lookup_drop_query (i' : spec.ι) (t' : spec.domain i') :
  (cache.drop_query i t).lookup i' t' = if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t' := rfl

@[simp] lemma drop_query_empty : drop_query i t ∅ = ∅ := by simpa [drop_query]

section order

lemma drop_query_monotone : monotone (drop_query i t) :=
λ cache cache' h i' t' u', by {simp only [lookup_drop_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

end order

end drop_query







-- @[simp] lemma drop_query_cache_query (i' : spec.ι) (t' : spec.domain i') :
--   [i, t ↦ u; cache].drop_query i' t' = if h : i = i' then
--     (if h.rec t = t' then cache else [i, t ↦ u; cache.drop_query i' t']) else [i, t ↦ u; cache.drop_query i' t'] :=
-- begin
--   sorry
-- end


-- lemma galois_connection_cache_query_drop_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
--   galois_connection (drop_query i t) (cache_query i t u) :=
-- begin
--   intros cache cache',
--   refine ⟨λ h, _, λ h, _⟩,
--   {

--   }
-- end


-- variables (i : spec.ι)


end query_cache
