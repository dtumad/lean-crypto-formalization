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

section lookup

variables (i : spec.ι) (t : spec.domain i)

/-- Get the currently cached value at the given input, or `none` if nothing is cached. -/
def lookup (cache : query_cache spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) := cache i t

@[ext] protected lemma ext {spec : oracle_spec} {cache cache' : query_cache spec}
  (h : ∀ (i : spec.ι) t, cache.lookup i t = cache'.lookup i t) : cache = cache' :=
funext (λ _, funext (λ _, h _ _))

protected lemma ext_iff {spec : oracle_spec} {cache cache' : query_cache spec} :
  cache = cache' ↔ ∀ (i : spec.ι) t, cache.lookup i t = cache'.lookup i t :=
⟨λ h i t, h ▸ rfl, query_cache.ext⟩

end lookup

section is_fresh

variables (i : spec.ι) (t : spec.domain i)

/-- `cache.is_fresh i t` means that there isn't any value cached for those inputs. -/
@[derive decidable]
def is_fresh (i : spec.ι) (t : spec.domain i) := (cache.lookup i t).is_none = tt

@[simp] lemma lookup_eq_none_iff_is_fresh : cache.lookup i t = none ↔ cache.is_fresh i t :=
by simp [is_fresh, option.is_none_iff_eq_none]

@[simp] lemma none_eq_lookup_iff_is_fresh : none = cache.lookup i t ↔ cache.is_fresh i t :=
eq_comm.trans (lookup_eq_none_iff_is_fresh cache i t)

lemma is_fresh_of_lookup_eq_none {i t} (h : cache.lookup i t = none) : cache.is_fresh i t :=
(lookup_eq_none_iff_is_fresh cache i t).1 h

lemma not_is_fresh_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  ¬ cache.is_fresh i t := by simp [is_fresh, h]

end is_fresh

section is_cached

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

/-- `cache.is_cached i t` means that there is *some* value cached for the inputs. -/
@[derive decidable]
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

@[simp] lemma lookup_ne_none_iff_is_cached : cache.lookup i t ≠ none ↔ cache.is_cached i t :=
by simp [is_cached_iff_not_is_fresh]

@[simp] lemma lookup_ne_none_iff_exists_lookup_eq_some :
  cache.lookup i t ≠ none ↔ ∃ u, cache.lookup i t = some u :=
by rw [lookup_ne_none_iff_is_cached, is_cached_iff_exists_lookup_eq_some]

end is_cached

section init

variables (i : spec.ι) (t : spec.domain i)

/-- `init spec` is the empty cache not containing any values yet (i.e. all are `none` still). -/
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
value cached in `cache'`. For uncached values the corresponding value can be anything.
We also have an `inf` operation that only returns values cached in both original caches. -/
instance : semilattice_inf (query_cache spec) :=
{ le := λ cache cache', ∀ i t u, cache.lookup i t = some u → cache'.lookup i t = some u,
  le_refl := λ cache i t u h, h,
  le_trans := λ cache cache' cache'' h h' i t u h'', h' i t u (h i t u h''),
  le_antisymm := λ cache cache' h' h, query_cache.ext (λ i t,
    begin
      by_cases hi : cache.lookup i t = none,
      { by_cases hi' : cache'.lookup i t = none,
        { rw [hi, hi'] },
        { obtain ⟨u, hu⟩ := option.ne_none_iff_exists'.1 hi',
          refine (option.some_ne_none u ((h i t u hu).symm.trans hi)).elim } },
      { exact let ⟨u, hu⟩ := option.ne_none_iff_exists'.1 hi in (hu.trans (h' i t u hu).symm) }
    end),
  inf := λ cache cache' i t, if cache.is_fresh i t ∨ cache'.is_fresh i t then none else
    (if cache.lookup i t = cache'.lookup i t then cache.lookup i t else none),
  inf_le_left := begin
    refine λ cache cache' i t u hu, _,
    by_cases h : cache.is_fresh i t ∨ cache'.is_fresh i t,
    { exact (option.some_ne_none _ (hu.symm.trans (by simp [lookup, h]))).elim },
    { have := (if_neg h).symm.trans hu,
      simp [ite_eq_iff', imp_false] at this,
      exact this.1 this.2 }
  end,
  inf_le_right := begin
    refine λ cache cache' i t u hu, _,
    by_cases h : cache.is_fresh i t ∨ cache'.is_fresh i t,
    { exact (option.some_ne_none _ (hu.symm.trans (by simp [lookup, h]))).elim },
    { have := (if_neg h).symm.trans hu,
      simp [ite_eq_iff', imp_false] at this,
      exact this.2.symm.trans (this.1 this.2) }
  end,
  le_inf := λ cache₁ cache₂ cache₃ h2 h3 i t u hu, trans (if_neg (not_or_distrib.2
    ⟨cache₂.not_is_fresh_of_lookup_eq_some (h2 i t u hu), cache₃.not_is_fresh_of_lookup_eq_some
      (h3 i t u hu)⟩)) (trans (if_pos ((h2 i t u hu).trans (h3 i t u hu).symm)) (h2 i t u hu)),

  }

lemma le_iff : cache ≤ cache' ↔ ∀ i t u, cache.lookup i t = some u → cache'.lookup i t = some u :=
iff.rfl

lemma lt_iff_le_and_exists : cache < cache' ↔ cache ≤ cache' ∧
  ∃ i t, cache.is_fresh i t ∧ cache'.is_cached i t :=
begin
  rw [lt_iff_le_and_ne],
  simp only [ne.def, and.congr_right_iff],
  intro h1,
  refine ⟨λ h, by_contra (λ h', h (query_cache.ext (λ i t, _))), λ h h', _⟩,
  { simp [is_cached_iff_not_is_fresh] at h',
    by_cases ht : cache.is_fresh i t,
    { calc cache.lookup i t = none : by simpa ... = cache'.lookup i t : by simpa using h' i t ht },
    { rw [← is_cached_iff_not_is_fresh, is_cached_iff_exists_lookup_eq_some] at ht,
      exact let ⟨u, hu⟩ := ht in hu.trans (h1 i t u hu).symm } },
  { obtain ⟨i, t, hi⟩ := h,
    rw [is_cached_iff_not_is_fresh, h'] at hi,
    exact hi.2 hi.1 }
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
by_contra (λ hs, let ⟨u, hu⟩ := (lookup_ne_none_iff_exists_lookup_eq_some _ _ _).1 hs in
  (option.some_ne_none u ((h i t u hu).symm.trans h')))

end order

section cache_query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

/-- Add a new value to the cache, erasing any old value if it already exists. -/
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

end cache_query

section drop_query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

/-- Set the cached value at the given input back to `none`. -/
def drop_query (i : spec.ι) (t : spec.domain i) (cache : query_cache spec) :
  query_cache spec := λ i' t', if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t'

@[simp] lemma lookup_drop_query (i' : spec.ι) (t' : spec.domain i') :
  (cache.drop_query i t).lookup i' t' = if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t' := rfl

@[simp] lemma drop_query_empty : drop_query i t ∅ = ∅ := by simpa [drop_query]

/-- Adding a value and then dropping it is the original cache if the added value was fresh,
and otherwise is the result of dropping the same query from the original cache,
since old cached values don't persist in the cache afterwords. -/
@[simp] lemma drop_query_cache_query :
  [i, t ↦ u; cache].drop_query i t = if cache.is_fresh i t then cache else cache.drop_query i t :=
sorry

/-- Adding a value to a cache after removing a value for the same inputs is the same as just
caching it into the original cache, since adding new values replaces old ones. -/
@[simp] lemma cache_query_drop_query : [i, t ↦ u; cache.drop_query i t] = [i, t ↦ u; cache] :=
sorry

end drop_query

section order_cache_query_drop_query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma cache_query_monotone : monotone (cache_query i t u) :=
λ cache cache' h i' t' u', by {simp only [lookup_cache_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

lemma drop_query_monotone : monotone (drop_query i t) :=
λ cache cache' h i' t' u', by {simp only [lookup_drop_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

@[simp] lemma le_singleton_iff : cache ≤ [i, t ↦ u] ↔ cache = ∅ ∨ cache = [i, t ↦ u] :=
begin
  sorry,
end

@[simp] lemma singleton_le_iff : [i, t ↦ u] ≤ cache ↔ cache.lookup i t = some u :=
begin
  sorry,
end

@[simp] lemma le_cache_query_iff : cache ≤ [i, t ↦ u; cache'] ↔
  (cache.is_fresh i t ∨ cache.lookup i t = some u) ∧
    (cache.drop_query i t ≤ cache'.drop_query i t) :=
begin
  sorry,
end

@[simp] lemma cache_query_le_iff : [i, t ↦ u; cache] ≤ cache' ↔
  cache'.lookup i t = some u ∧ cache.drop_query i t ≤ cache' :=
begin
  sorry
end

end order_cache_query_drop_query

end query_cache
