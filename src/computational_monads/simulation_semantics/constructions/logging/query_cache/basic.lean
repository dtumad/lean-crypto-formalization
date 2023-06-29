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

/-- Have `simp` normalize towards using `lookup` over direct application. -/
@[simp] lemma apply_eq_lookup (i t) : cache i t = cache.lookup i t := rfl

@[ext] protected lemma ext {cache cache' : query_cache spec}
  (h : ∀ i t, cache.lookup i t = cache'.lookup i t) : cache = cache' :=
funext (λ _, funext (λ _, h _ _))

protected lemma ext_iff : cache = cache' ↔ ∀ i t, cache.lookup i t = cache'.lookup i t :=
⟨λ h i t, h ▸ rfl, query_cache.ext⟩

lemma ne_iff_exists_lookup_ne : cache ≠ cache' ↔ ∃ i t, cache.lookup i t ≠ cache'.lookup i t :=
function.ne_iff.trans ⟨λ h, let ⟨i, hi⟩ := h in let ⟨t, ht⟩ := function.ne_iff.1 hi in ⟨i, t, ht⟩,
  λ h, let ⟨i, t, ht⟩ := h in ⟨i, function.ne_iff.2 ⟨t, ht⟩⟩⟩

lemma ne_of_lookup_ne (i t) (h : cache.lookup i t ≠ cache'.lookup i t) : cache ≠ cache' :=
(ne_iff_exists_lookup_ne cache cache').2 ⟨i, t, h⟩

lemma lookup_ne_some_of_lookup_eq_none {i t} (h : cache.lookup i t = none)
  (u : spec.range i) : cache.lookup i t ≠ some u :=
λ hu, (option.some_ne_none u (hu.symm.trans h))

lemma lookup_ne_none_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  cache.lookup i t ≠ none := λ hu, (option.some_ne_none u (h.symm.trans hu))

end lookup

section is_fresh

/-- `cache.is_fresh i t` means that there isn't any value cached for those inputs. -/
@[derive decidable]
def is_fresh (i : spec.ι) (t : spec.domain i) := (cache.lookup i t).is_none = tt

@[simp] lemma lookup_eq_none_iff_is_fresh (i t) : cache.lookup i t = none ↔ cache.is_fresh i t :=
by simp [is_fresh, option.is_none_iff_eq_none]

@[simp] lemma none_eq_lookup_iff_is_fresh (i t) : none = cache.lookup i t ↔ cache.is_fresh i t :=
eq_comm.trans (lookup_eq_none_iff_is_fresh cache i t)

lemma is_fresh_of_lookup_eq_none {i t} (h : cache.lookup i t = none) : cache.is_fresh i t :=
(lookup_eq_none_iff_is_fresh cache i t).1 h

@[simp] lemma lookup_eq_none_of_is_fresh {i t} (h : cache.is_fresh i t) : cache.lookup i t = none :=
(cache.lookup_eq_none_iff_is_fresh i t).2 h

lemma not_is_fresh_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  ¬ cache.is_fresh i t := by simp [is_fresh, h]

lemma lookup_ne_some_of_is_fresh {i t} (h : cache.is_fresh i t) (u : spec.range i) :
  cache.lookup i t ≠ some u := by simp [h]

lemma is_fresh_of_is_fresh_of_lookup_eq {i t} (h : cache.is_fresh i t)
  (h' : cache.lookup i t = cache'.lookup i t) : cache'.is_fresh i t :=
begin
  rw [← lookup_eq_none_iff_is_fresh] at ⊢ h,
  exact h'.symm.trans h
end

end is_fresh

section is_cached

/-- `cache.is_cached i t` means that there is *some* value cached for the inputs. -/
@[derive decidable]
def is_cached (i : spec.ι) (t : spec.domain i) := (cache.lookup i t).is_some = tt

@[simp] lemma not_is_cached_iff_is_fresh (i t) : ¬ cache.is_cached i t ↔ cache.is_fresh i t :=
by rw [is_cached, option.not_is_some_iff_eq_none, lookup_eq_none_iff_is_fresh]

@[simp]  lemma not_is_fresh_iff_is_cached (i t) : ¬ cache.is_fresh i t ↔ cache.is_cached i t :=
by rw [← not_is_cached_iff_is_fresh, not_not]

lemma not_is_cached_of_is_fresh {i t} (h : cache.is_fresh i t) : ¬ cache.is_cached i t :=
(not_is_cached_iff_is_fresh cache i t).2 h

lemma is_fresh_of_not_is_cached {i t} (h : ¬ cache.is_cached i t) : cache.is_fresh i t :=
(not_is_cached_iff_is_fresh cache i t).1 h

lemma not_is_fresh_of_is_cached {i t} (h : cache.is_cached i t) : ¬ cache.is_fresh i t :=
(not_is_fresh_iff_is_cached cache i t).2 h

lemma is_cached_of_not_is_fresh {i t} (h : ¬ cache.is_fresh i t) : cache.is_cached i t :=
(not_is_fresh_iff_is_cached cache i t).1 h

lemma is_cached_iff_exists_lookup_eq_some (i t) :
  cache.is_cached i t ↔ ∃ u, cache.lookup i t = some u :=
by simp [is_cached, ← option.is_some_iff_exists]

lemma not_is_fresh_iff_exists_lookup_eq_some (i t) :
  ¬ cache.is_fresh i t ↔ ∃ u, cache.lookup i t = some u :=
by simp [is_cached_iff_exists_lookup_eq_some]

lemma is_cached_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  cache.is_cached i t := (is_cached_iff_exists_lookup_eq_some cache i t).2 ⟨u, h⟩

lemma lookup_eq_some_of_is_cached {i t} (h : cache.is_cached i t) :
  ∃ u, cache.lookup i t = some u := (cache.is_cached_iff_exists_lookup_eq_some i t).1 h

lemma not_is_cached_of_lookup_eq_none {i t} (h : cache.lookup i t = none) :
  ¬ cache.is_cached i t := by simp [is_cached, h]

lemma lookup_eq_none_of_not_is_cached {i t} (h : ¬ cache.is_cached i t) :
  cache.lookup i t = none := lookup_eq_none_of_is_fresh cache (is_fresh_of_not_is_cached _ h)

lemma lookup_ne_none_iff_is_cached (i t) :
  cache.lookup i t ≠ none ↔ cache.is_cached i t := by simp

lemma lookup_ne_none_iff_exists_lookup_eq_some {i t} :
  cache.lookup i t ≠ none ↔ ∃ u, cache.lookup i t = some u :=
by simp [is_cached_iff_exists_lookup_eq_some]

@[simp] lemma some_get_or_else_lookup_of_is_cached {i t u} (h : cache.is_cached i t) :
  some ((cache.lookup i t).get_or_else u) = cache.lookup i t :=
let ⟨u, hu⟩ := lookup_eq_some_of_is_cached _ h in by simp [hu]

lemma is_cached_of_is_cached_of_lookup_eq {i t} (h' : cache.is_cached i t)
  (h : cache.lookup i t = cache'.lookup i t) : cache'.is_cached i t :=
begin
  rw [is_cached_iff_exists_lookup_eq_some] at h' ⊢,
  exact let ⟨u, hu⟩ := h' in ⟨u, h.symm.trans hu⟩
end

end is_cached

section init

/-- `init spec` is the empty cache not containing any values yet (i.e. all are `none` still). -/
protected def init (spec : oracle_spec) : query_cache spec := λ _ _, none

variables (i : spec.ι) (t : spec.domain i)

instance : has_emptyc (query_cache spec) := ⟨query_cache.init spec⟩

instance : inhabited (query_cache spec) := ⟨∅⟩

lemma init_apply' : (∅ : query_cache spec) i = λ _, none := rfl

@[simp] lemma init_apply : (∅ : query_cache spec) i t = none := rfl

@[simp] lemma lookup_init : lookup ∅ i t = none := rfl

lemma lookup_init_ne_some (u : spec.range i) : lookup ∅ i t ≠ some u := by simp

@[simp] lemma is_fresh_init : is_fresh ∅ i t := by simp [is_fresh]

@[simp] lemma not_is_cached_init : ¬ is_cached ∅ i t := by simp [is_cached]

@[simp] lemma eq_init_iff_forall_is_fresh : cache = ∅ ↔ ∀ i t, cache.is_fresh i t :=
by simp [query_cache.ext_iff]

lemma eq_init_iff_forall_eq_none : cache = ∅ ↔ ∀ i t, cache.lookup i t = none := by simp

lemma ne_init_iff_exists_is_cached : cache ≠ ∅ ↔ ∃ i t, cache.is_cached i t := by simp

lemma ne_init_iff_exists_eq_some : cache ≠ ∅ ↔ ∃ i t u, cache.lookup i t = some u :=
by simp [is_cached_iff_exists_lookup_eq_some]

end init

section cache_query

/-- Add a new value to the cache, erasing any old value if it already exists. -/
def cache_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) (cache : query_cache spec) :
  query_cache spec := λ i' t', if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t'

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

notation `[` i `,` t `↦` u `;` cache `]` := cache_query i t u cache

lemma lookup_cache_query (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t' := rfl

@[simp] lemma lookup_cache_query_same_index (t' : spec.domain i) :
  [i, t ↦ u; cache].lookup i t' = if t = t' then some u else cache.lookup i t' :=
by simp [lookup_cache_query]

@[simp] lemma lookup_cache_query_diff_index (i' : spec.ι) (t' : spec.domain i') (hi : i ≠ i') :
  [i, t ↦ u; cache].lookup i' t' = cache.lookup i' t' := by simp [lookup_cache_query, hi]

lemma lookup_cache_query_same_input : [i, t ↦ u; cache].lookup i t = some u := by simp

@[simp] lemma lookup_cache_query_diff_input (t' : spec.domain i) (ht : t ≠ t') :
  [i, t ↦ u; cache].lookup i t' = cache.lookup i t' := by simp [ht]

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

lemma is_fresh_cache_query_same_index_iff (t' : spec.domain i) :
  [i, t ↦ u; cache].is_fresh i t' ↔ cache.is_fresh i t' ∧ t ≠ t' := by simp

lemma not_is_fresh_cache_query_same_input : ¬ [i, t ↦ u; cache].is_fresh i t := by simp

@[simp] lemma is_cached_cache_query_iff (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache].is_cached i' t' ↔ cache.is_cached i' t' ∨
    (if h : i = i' then h.rec t = t' else false) :=
begin
  rw [← not_is_fresh_iff_is_cached, is_fresh_cache_query_iff,
    not_and_distrib, not_is_fresh_iff_is_cached],
  split_ifs; simp
end

lemma is_cached_cache_query_same_index_iff (t' : spec.domain i) :
  [i, t ↦ u; cache].is_cached i t' ↔ cache.is_cached i t' ∨ t = t' := by simp

lemma is_cached_cache_query_same_input : [i, t ↦ u; cache].is_cached i t := by simp

lemma cache_query_inj_of_is_fresh (h : cache.is_fresh i t) (h' : cache'.is_fresh i t) :
  [i, t ↦ u; cache] = [i, t ↦ u; cache'] ↔ cache = cache' :=
begin
  simp only [query_cache.ext_iff],
  refine ⟨λ hc i' t', _, λ hc i' t', _⟩,
  { by_cases hi : i = i',
    { induction hi,
      by_cases ht : t = t',
      { simp [← ht, h, h'] },
      { simpa [ht] using hc i t' } },
    { simpa [hi] using hc i' t' } },
  { by_cases hi : i = i',
    { induction hi,
      by_cases ht : t = t',
      { simp [ht] },
      { simpa [ht] using hc i t' } },
    { simpa [hi] using hc i' t' } }
end

end cache_query

section drop_query

/-- Set the cached value at the given input back to `none`. -/
def drop_query (i : spec.ι) (t : spec.domain i) (cache : query_cache spec) :
  query_cache spec := λ i' t', if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t'

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma lookup_drop_query (i' : spec.ι) (t' : spec.domain i') :
  (cache.drop_query i t).lookup i' t' = if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t' := rfl

@[simp] lemma lookup_drop_query_same_index (t' : spec.domain i) :
  (cache.drop_query i t).lookup i t' = if t = t' then none else cache.lookup i t' :=
by simp [lookup_drop_query]

@[simp] lemma lookup_drop_query_diff_index (i' : spec.ι) (t' : spec.domain i') (hi : i ≠ i') :
  (cache.drop_query i t).lookup i' t' = cache.lookup i' t' := by simp [lookup_drop_query, hi]

lemma lookup_drop_query_same_input : (cache.drop_query i t).lookup i t = none := by simp

lemma lookup_drop_query_diff_input (t' : spec.domain i) (ht : t ≠ t'):
  (cache.drop_query i t).lookup i t' = cache.lookup i t' := by simp [ht]

@[simp] lemma drop_query_of_is_fresh (h : cache.is_fresh i t) : cache.drop_query i t = cache :=
begin
  refine query_cache.ext (λ i t, _),
  simp [lookup_drop_query],
  rintros rfl rfl,
  exact h,
end

@[simp] lemma is_fresh_drop_query_iff (i' : spec.ι) (t' : spec.domain i') :
  (cache.drop_query i t).is_fresh i' t' ↔ cache.is_fresh i' t' ∨ ∃ (h : i = i'), h.rec t = t' :=
begin
  refine ⟨λ h, _, λ h, (lookup_eq_none_iff_is_fresh _ _ _).1 (h.rec_on (λ h', _) _)⟩,
  { by_cases hi : i = i',
    { induction hi,
      by_cases ht : t = t',
      { exact or.inr ⟨rfl, ht⟩ },
      { simp_rw [← lookup_eq_none_iff_is_fresh, lookup_drop_query_same_index, ht,
          if_false, lookup_eq_none_iff_is_fresh] at h,
        exact or.inl h } },
    { refine or.inl _,
      simpa [lookup_drop_query, hi, if_false] using ((lookup_eq_none_iff_is_fresh _ _ _).2 h) } },
  { { by_cases hi : i = i',
      { induction hi,
        by_cases ht : t = t',
        { simp [ht, lookup_drop_query_same_input _ _ _] },
        { simpa [lookup_drop_query_diff_input _ _ _ _ ht] } },
      { simpa [lookup_drop_query_diff_index _ _ _ _ _ hi] } } },
  { rintro ⟨rfl, rfl⟩,
    simp }
end

lemma is_fresh_drop_query_iff_same_index (t' : spec.domain i) :
  (cache.drop_query i t).is_fresh i t' ↔ cache.is_fresh i t' ∨ t = t' := by simp

lemma is_fresh_drop_query_iff_diff_index (i' : spec.ι) (t' : spec.domain i') (h : i ≠ i') :
  (cache.drop_query i t).is_fresh i' t' ↔ cache.is_fresh i' t' := by simp [h]

lemma is_fresh_drop_query_same_input : (cache.drop_query i t).is_fresh i t := by simp

lemma is_fresh_drop_query_iff_diff_input (t' : spec.domain i) (h : t ≠ t') :
  (cache.drop_query i t).is_fresh i t' ↔ cache.is_fresh i t' := by simp [h]

@[simp] lemma drop_query_init : drop_query i t ∅ = ∅ := by simp

end drop_query

section drop_query_cache_query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

/-- Adding a query to the cache and then dropping a query commutes to dropping and then adding,
unless the inputs being cached are the same as the one being dropped. -/
@[simp] lemma drop_query_cache_query (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache].drop_query i' t' = if h : i = i' then (if h.rec t = t' then cache.drop_query i' t'
    else [i, t ↦ u; cache.drop_query i' t']) else [i, t ↦ u; cache.drop_query i' t'] :=
begin
  simp only [query_cache.ext_iff],
  intros i'' t'',
  by_cases hi : i = i',
  { induction hi,
    by_cases hi' : i = i'',
    { induction hi',
      by_cases ht : t = t',
      { by_cases ht' : t' = t'',
        { simp [ht, ht'] },
        { simp [ht, ht'] } },
      { by_cases ht' : t' = t'',
        { simp [ht, ht', (ht' ▸ ht : t ≠ t'')] },
        { simp [ht, ht'] } } },
    { by_cases ht : t = t',
      { simp [hi', ht] },
      { simp [hi', ht] } } },
  { by_cases hi' : i' = i'',
    { induction hi',
      simp [hi] },
    { by_cases hi'' : i = i'',
      { induction hi'',
        simp [hi, hi'] },
      { simp [hi, hi', hi''] } } }
end

lemma drop_query_cache_query_same_index (t' : spec.domain i) (u' : spec.domain i) :
  [i, t ↦ u; cache].drop_query i t' =
    if t = t' then cache.drop_query i t' else [i, t ↦ u; cache.drop_query i t'] := by simp

lemma drop_query_cache_query_diff_index (i' : spec.ι) (t' : spec.domain i') (h : i ≠ i') :
  [i, t ↦ u; cache].drop_query i' t' = [i, t ↦ u; cache.drop_query i' t'] := by simp [h]

lemma drop_query_cache_query_same_input :
  [i, t ↦ u; cache].drop_query i t = cache.drop_query i t := by simp

lemma drop_query_cache_query_diff_input (t' : spec.domain i) (h : t ≠ t') :
  [i, t ↦ u; cache].drop_query i t' = [i, t ↦ u; cache.drop_query i t'] := by simp [h]

end drop_query_cache_query

section cache_query_drop_query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma cache_query_drop_query (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u; cache.drop_query i' t'] = if h : i = i' then (if h.rec t = t' then [i, t ↦ u; cache]
    else [i, t ↦ u; cache].drop_query i' t') else [i, t ↦ u; cache].drop_query i' t' :=
begin
  by_cases hi : i = i',
  {
    induction hi,
    by_cases ht : t = t',
    {
      simp [ht],
    }
  }
end

/-- Adding a value to a cache after removing a value for the same inputs is the same as just
caching it into the original cache, since adding new values replaces old ones. -/
@[simp] lemma cache_query_drop_query_same_input :
  [i, t ↦ u; cache.drop_query i t] = [i, t ↦ u; cache] :=
begin

end

end cache_query_drop_query

lemma cache_query_eq_cache_query_iff_drop_query_eq_drop_query (i t u) :
  [i, t ↦ u; cache] = [i, t ↦ u; cache'] ↔ cache.drop_query i t = cache'.drop_query i t :=
⟨λ h, by simpa only [drop_query_cache_query, eq_self_iff_true] using
  congr_arg (λ c, drop_query i t c) h, λ h, by simpa only [cache_query_drop_query_same_input] using
    congr_arg (λ c, [i, t ↦ u; c]) h⟩

section singleton

/-- Query cache with exactly one cached value given by the inputs -/
def singleton (i : spec.ι) (t : spec.domain i) (u : spec.range i) := [i, t ↦ u; ∅]

notation `[` i `,` t `↦` u `]` := singleton i t u

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma singleton.def : [i, t ↦ u] = [i, t ↦ u; ∅] := rfl

lemma lookup_singleton (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else none) else none := rfl

@[simp] lemma lookup_singleton_same_index (t' : spec.domain i) :
  [i, t ↦ u].lookup i t' = if t = t' then some u else none := by simp [lookup_singleton]

@[simp] lemma lookup_singleton_diff_index (i' : spec.ι) (t' : spec.domain i') (h : i ≠ i') :
  [i, t ↦ u].lookup i' t' = none := by simp [lookup_singleton, h]

lemma lookup_singleton_same_input :
  [i, t ↦ u].lookup i t = some u := by simp

@[simp] lemma lookup_singleton_diff_input (t' : spec.domain i) (h : t ≠ t') :
  [i, t ↦ u].lookup i t' = none := by simp [h]

lemma lookup_singleton_eq_some_iff (i' : spec.ι) (t' : spec.domain i')
  (u' : spec.range i') : [i, t ↦ u].lookup i' t' = some u' ↔
    ∃ (h : i = i'), h.rec t = t' ∧ h.rec u = u' :=
by simp [lookup_singleton, dite_eq_iff, ite_eq_iff]

lemma lookup_singleton_eq_some_iff_same_index (t' : spec.domain i) (u' : spec.range i) :
  [i, t ↦ u].lookup i t' = some u' ↔ t = t' ∧ u = u' :=
by simp [lookup_singleton_eq_some_iff, ite_eq_iff]

lemma lookup_singleton_eq_some_iff_same_input (u' : spec.range i) :
  [i, t ↦ u].lookup i t = some u' ↔ u = u' := by simp

lemma singleton_ne_init : [i, t ↦ u] ≠ ∅ := cache_query_ne_init ∅ i t u

@[simp] lemma is_fresh_singleton_iff (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u].is_fresh i' t' ↔ if h : i = i' then h.rec t ≠ t' else true := by simp [singleton.def]

lemma is_fresh_singleton_iff_same_index (t' : spec.domain i) :
  [i, t ↦ u].is_fresh i t' ↔ t ≠ t' := by simp

lemma is_fresh_singleton_diff_index (i' : spec.ι) (t' : spec.domain i') (h : i ≠ i') :
  [i, t ↦ u].is_fresh i' t' := by simp [h]

lemma not_is_fresh_singleton_same_input : ¬ [i, t ↦ u].is_fresh i t := by simp

lemma is_fresh_singleton_diff_input (t' : spec.domain i) (h : t ≠ t') :
  [i, t ↦ u].is_fresh i t' := by simp [h]

@[simp] lemma drop_query_singleton (i' : spec.ι) (t' : spec.domain i') :
  [i, t ↦ u].drop_query i' t' = if h : i = i' then (if h.rec t = t' then ∅
    else [i, t ↦ u]) else [i, t ↦ u] :=
by simp [singleton.def]

lemma drop_query_singleton_same_index (t' : spec.domain i) :
  [i, t ↦ u].drop_query i t' = if t = t' then ∅ else [i, t ↦ u] := by simp

lemma drop_query_singleton_diff_index (i' : spec.ι) (t' : spec.domain i') (h : i ≠ i') :
  [i, t ↦ u].drop_query i' t' = [i, t ↦ u] := by simp [h]

lemma drop_query_singleton_same_input : [i, t ↦ u].drop_query i t = ∅ := by simp

lemma drop_query_singleton_diff_input (t' : spec.domain i) (h : t ≠ t') :
  [i, t ↦ u].drop_query i t' = [i, t ↦ u] := by simp [h]

end singleton

end query_cache
