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

/-- Get the currently cached value at the given input, or `none` if nothing is cached. -/
def lookup (cache : query_cache spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) := cache i t

variables (i : spec.ι) (t : spec.domain i)

@[ext] protected lemma ext {spec : oracle_spec} {cache cache' : query_cache spec}
  (h : ∀ (i : spec.ι) t, cache.lookup i t = cache'.lookup i t) : cache = cache' :=
funext (λ _, funext (λ _, h _ _))

protected lemma ext_iff {spec : oracle_spec} {cache cache' : query_cache spec} :
  cache = cache' ↔ ∀ (i : spec.ι) t, cache.lookup i t = cache'.lookup i t :=
⟨λ h i t, h ▸ rfl, query_cache.ext⟩

lemma ne_iff_exists_lookup_ne : cache ≠ cache' ↔ ∃ i t, cache.lookup i t ≠ cache'.lookup i t :=
function.ne_iff.trans ⟨λ h, let ⟨i, hi⟩ := h in let ⟨t, ht⟩ := function.ne_iff.1 hi in ⟨i, t, ht⟩,
  λ h, let ⟨i, t, ht⟩ := h in ⟨i, function.ne_iff.2 ⟨t, ht⟩⟩⟩

lemma ne_of_lookup_ne (i : spec.ι) (t : spec.domain i)
  (h : cache.lookup i t ≠ cache'.lookup i t) : cache ≠ cache' :=
(ne_iff_exists_lookup_ne cache cache').2 ⟨i, t, h⟩

end lookup

section is_fresh

/-- `cache.is_fresh i t` means that there isn't any value cached for those inputs. -/
@[derive decidable]
def is_fresh (i : spec.ι) (t : spec.domain i) := (cache.lookup i t).is_none = tt

variables (i : spec.ι) (t : spec.domain i)

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

/-- `cache.is_cached i t` means that there is *some* value cached for the inputs. -/
@[derive decidable]
def is_cached (i : spec.ι) (t : spec.domain i) := (cache.lookup i t).is_some = tt

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

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

/-- `init spec` is the empty cache not containing any values yet (i.e. all are `none` still). -/
@[inline, reducible] protected def init (spec : oracle_spec) :
  query_cache spec := λ _ _, none

variables (i : spec.ι) (t : spec.domain i)

instance : has_emptyc (query_cache spec) := ⟨query_cache.init spec⟩

instance : inhabited (query_cache spec) := ⟨∅⟩

lemma init_apply' : (∅ : query_cache spec) i = λ _, none := rfl

lemma init_apply : (∅ : query_cache spec) i t = none := rfl

@[simp] lemma lookup_init : lookup ∅ i t = none := rfl

lemma lookup_init_ne_some (u : spec.range i) : lookup ∅ i t ≠ some u := by simp

@[simp] lemma is_fresh_init : is_fresh ∅ i t := by simp [is_fresh]

@[simp] lemma not_is_cached_init : ¬ is_cached ∅ i t := by simp [is_cached]

@[simp] lemma eq_init_iff : cache = ∅ ↔ ∀ i t, cache.is_fresh i t :=
by simp [query_cache.ext_iff]

lemma eq_init_iff' : cache = ∅ ↔ ∀ i t, cache.lookup i t = none :=
by simp [query_cache.ext_iff]

lemma ne_init_iff : cache ≠ ∅ ↔ ∃ i t, cache.is_cached i t :=
by simp [eq_init_iff, is_cached_iff_not_is_fresh]

lemma ne_init_iff' : cache ≠ ∅ ↔ ∃ i t u, cache.lookup i t = some u :=
by simp [eq_init_iff, ne.def, ← is_cached_iff_not_is_fresh, is_cached_iff_exists_lookup_eq_some]

end init

section order -- TODO: `is_mono` typeclass for `sim_oracle`.

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
      (h3 i t u hu)⟩)) (trans (if_pos ((h2 i t u hu).trans (h3 i t u hu).symm)) (h2 i t u hu)) }

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

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

@[simp] lemma init_le : ∅ ≤ cache := bot_le

lemma init_le' {cache : query_cache spec} : ∅ ≤ cache := bot_le

@[simp] lemma init_lt_iff : ∅ < cache ↔ cache ≠ ∅ := bot_lt_iff_ne_bot

@[simp] lemma le_init_iff : cache ≤ ∅ ↔ cache = ∅ := le_bot_iff

@[simp] lemma not_lt_init : ¬ cache < ∅ := not_lt_bot

@[simp] lemma inf_init : cache ⊓ ∅ = ∅ := inf_bot_eq

@[simp] lemma init_inf : ∅ ⊓ cache = ∅ := bot_inf_eq

lemma lookup_eq_some_of_le (h : cache ≤ cache')
  (h' : cache.lookup i t = some u) : cache'.lookup i t = some u :=
h i t u h'

lemma lookup_eq_none_of_le (h : cache ≤ cache')
  (h' : cache'.lookup i t = none) : cache.lookup i t = none :=
by_contra (λ hs, let ⟨u, hu⟩ := (lookup_ne_none_iff_exists_lookup_eq_some _ _ _).1 hs in
  (option.some_ne_none u ((h i t u hu).symm.trans h')))

end order

section cache_query

/-- Add a new value to the cache, erasing any old value if it already exists. -/
def cache_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) (cache : query_cache spec) :
  query_cache spec := λ i' t', if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t'

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

notation `[` i `,` t `↦` u `;` cache `]` := cache_query i t u cache

@[simp] lemma lookup_cache_query (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t' := rfl

lemma lookup_cache_query_same_index (t' : spec.domain i) :
  [i, t ↦ u; cache].lookup i t' = if t = t' then some u else cache.lookup i t' := by simp

lemma lookup_cache_query_same_input : [i, t ↦ u; cache].lookup i t = some u := by simp

@[simp] lemma cache_query_ne_init : [i, t ↦ u; cache] ≠ ∅ :=
ne_of_lookup_ne _ _ i t (by simp)

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
by {rw [is_cached_iff_not_is_fresh, is_fresh_cache_query_iff, not_and_distrib,
  ← is_cached_iff_not_is_fresh], split_ifs; simp only [not_not, not_true] }

end cache_query

section singleton

-- Special notation for cache containing a single value.
notation `[` i `,` t `↦` u `]` := cache_query i t u ∅

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma lookup_singleton (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else none) else none := rfl

lemma lookup_singleton_same_index (t' : spec.domain i) :
  [i, t ↦ u].lookup i t' = if t = t' then some u else none := by simp

lemma lookup_singleton_same_input : [i, t ↦ u].lookup i t = some u := by simp

lemma lookup_singleton_eq_some_iff (i' : spec.ι) (t' : spec.domain i') (u' : spec.range i') :
  [i, t ↦ u].lookup i' t' = some u' ↔ ∃ (h : i = i'), h.rec t = t' ∧ h.rec u = u' :=
begin
  rw [lookup_singleton],
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t'; simp [ht] },
  { simp [hi] }
end

@[simp] lemma lookup_singleton_eq_some_iff_of_same_index (t' : spec.domain i) (u' : spec.range i) :
  [i, t ↦ u].lookup i t' = some u' ↔ t = t' ∧ u = u' :=
by simp [lookup_singleton_eq_some_iff, ite_eq_iff]

lemma eq_singleton_iff : cache = [i, t ↦ u] ↔ cache ≤ [i, t ↦ u] ∧ cache ≠ ∅ :=
begin
  refine ⟨λ h, h.symm ▸ by simp, λ h, le_antisymm h.1 (λ i' t' u' h', _)⟩,
  obtain ⟨i'', t'', u'', h''⟩ := (ne_init_iff' _).1 h.2,
  have := h.1 i'' t'' u'' h'',
  rw [lookup_singleton_eq_some_iff] at this h',
  obtain ⟨hi, ht, hu⟩ := this,
  obtain ⟨hi', ht', hu'⟩ := h',
  induction hi,
  induction hi',
  rwa [← ht', ← hu', ht, hu],
end

lemma singleton_ne_init : [i, t ↦ u] ≠ ∅ := cache_query_ne_init ∅ i t u

@[simp] lemma le_singleton_iff : cache ≤ [i, t ↦ u] ↔ cache = ∅ ∨ cache = [i, t ↦ u] :=
begin
  rw [eq_singleton_iff, and_comm],
  refine ⟨λ h, _, λ h, h.rec_on (λ h', le_of_eq_of_le h' (init_le _)) (λ h, h.2)⟩,
  by_cases h' : cache = ∅,
  { exact or.inl h' },
  { exact or.inr ⟨h', h⟩ }
end

lemma le_singleton_iff_forall : cache ≤ [i, t ↦ u] ↔
  ∀ i' t', cache.is_cached i' t' → ∃ (h : i = i'), h.rec t = t' :=
begin
  refine ⟨λ h i' t' ht', _, λ h, _⟩,
  {
    have := is_cached_iff_exists_lookup_eq_some
  }
end

@[simp] lemma lt_singleton_iff : cache < [i, t ↦ u] ↔ cache = ∅ :=
begin
  rw [lt_iff_le_and_ne, le_singleton_iff, or_and_distrib_right,
    and_not_self, or_false, and_iff_left_iff_imp],
  exact λ h, h.symm ▸ (ne.symm (singleton_ne_init i t u))
end

@[simp] lemma singleton_le_iff : [i, t ↦ u] ≤ cache ↔ cache.lookup i t = some u :=
begin
  refine ⟨λ h, h i t u (lookup_singleton_same_input i t u), λ h i' t' u' h', _⟩,
  obtain ⟨hi, ht, hu⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 h',
  induction hi,
  refine ht ▸ hu ▸ h
end

end singleton

section drop_query

/-- Set the cached value at the given input back to `none`. -/
def drop_query (i : spec.ι) (t : spec.domain i) (cache : query_cache spec) :
  query_cache spec := λ i' t', if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t'

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

@[simp] lemma lookup_drop_query (i' : spec.ι) (t' : spec.domain i') :
  (cache.drop_query i t).lookup i' t' = if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t' := rfl

@[simp] lemma is_fresh_drop_query_iff (i' : spec.ι) (t' : spec.domain i') :
  (cache.drop_query i t).is_fresh i' t' ↔ cache.is_fresh i' t' ∨ ∃ (h : i = i'), h.rec t = t' :=
begin
  sorry,
end

lemma drop_query_of_is_fresh (h : cache.is_fresh i t) :
  cache.drop_query i t = cache :=
begin
  sorry,
end

@[simp] lemma drop_query_init : drop_query i t ∅ = ∅ := by simp

@[simp] lemma drop_query_eq_init_iff : drop_query i t cache = ∅ ↔
  ∃ u, cache ≤ [i, t ↦ u] :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    by_cases h' : cache.is_fresh i t,
    { rw [drop_query_of_is_fresh _ _ _ h'] at h,
      exact ⟨default, h.symm ▸ init_le'⟩ },
    {
      rw [← is_cached_iff_not_is_fresh, is_cached_iff_exists_lookup_eq_some] at h',
      obtain ⟨u, hu⟩ := h',
      refine ⟨u, _⟩,
      rw [eq_init_iff] at h,
      intros i' t' u' hu',
      specialize h i' t',
      rw [is_fresh_drop_query_iff, ← lookup_eq_none_iff_is_fresh] at h,
      refine h.rec_on (λ h', (option.some_ne_none u' (hu'.symm.trans h')).elim) _,
      rintro ⟨rfl, rfl⟩,
      have := hu'.symm.trans hu,
      rw [option.some_inj] at this,
      refine this ▸ (lookup_singleton_same_input _ _ _),

    }
  },
  {
    obtain ⟨u, hu⟩ := h,
    rw [eq_init_iff],
    intros i' t',
    rw [is_fresh_drop_query_iff, or_iff_not_imp_left, ← is_cached_iff_not_is_fresh,
      is_cached_iff_exists_lookup_eq_some],
    rintro ⟨u', hu'⟩,
    specialize hu i' t' u' hu',
    rw [lookup_singleton_eq_some_iff] at hu,
    obtain ⟨hi', ht', hu'⟩ := hu,
    refine ⟨hi', ht'⟩,
  }
end

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
