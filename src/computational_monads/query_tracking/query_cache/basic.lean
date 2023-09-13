/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec

/-!
# Cache for Oracle Queries

This file defines a `query_cache` type for storing oracle queries and recalling cached values.
We construct them as functions from oracle indices and inputs to optional output values.
This automatically gives order independence of cache values and uniqeness of cache values.
Updates are done using continuation passing with the previous cache.

We also define a number of basic constructors and operations on `query_cache`:
* `query_cache.lookup` returns the currently cached value.
* `query_cache.mem_inputs` is true iff the given value is cached.
* `query_cache.cache_query` add a value to the cache.
* `query_cache.drop_query` removes a value from the cache.
* `query_cache.empty` has no cached inputs at all.
-/

namespace oracle_spec

/-- Data type representing a cache of oracle queries for a given `oracle_spec`,
represented as a function from inputs to optional outputs, with `none` meaning an uncached value.
We also bundle a finset `cached_inputs` containing all the currently cached values,
which is enforced by the included proof in `mem_cached_inputs`, since we generally only
consider computations with a bounded number of oracle queries. -/
@[ext] structure query_cache (spec : oracle_spec) : Type :=
(cache_fn : Π (i : spec.ι), spec.domain i → option (spec.range i))
(cached_inputs : finset (Σ (i : spec.ι), spec.domain i))
(mem_cached_inputs (x : Σ i, spec.domain i) : x ∈ cached_inputs ↔ cache_fn x.1 x.2 ≠ none)

namespace query_cache

open oracle_spec

variables {spec : oracle_spec} (cache cache' : query_cache spec)

section lookup

/-- Get the currently cached value at the given input, or `none` if nothing is cached.
TODO: can just call the field itself lookup at this point. -/
def lookup (cache : query_cache spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) := cache.cache_fn i t

/-- Have `simp` normalize towards using `lookup` over direct application. -/
@[simp] lemma apply_eq_lookup (i t) : cache.cache_fn i t = cache.lookup i t := rfl

/-- Two caches are equal if all queries have the same `lookup` value. -/
@[ext] protected lemma extₗ {cache cache' : query_cache spec}
  (h : ∀ i t, cache.lookup i t = cache'.lookup i t) : cache = cache' :=
query_cache.ext _ _ (funext (λ _, funext (λ _, h _ _)))
  (by simp [finset.ext_iff, mem_cached_inputs, h])

protected lemma ext_iffₗ : cache = cache' ↔ ∀ i t, cache.lookup i t = cache'.lookup i t :=
⟨λ h i t, h ▸ rfl, query_cache.extₗ⟩

lemma ne_iff_exists_lookup_ne : cache ≠ cache' ↔ ∃ i t, cache.lookup i t ≠ cache'.lookup i t :=
by simp only [ne.def, query_cache.ext_iffₗ, not_forall]

lemma ne_of_lookup_ne (i t) (h : cache.lookup i t ≠ cache'.lookup i t) : cache ≠ cache' :=
(ne_iff_exists_lookup_ne cache cache').2 ⟨i, t, h⟩

lemma lookup_ne_some_of_lookup_eq_none {i t} (h : cache.lookup i t = none)
  (u : spec.range i) : cache.lookup i t ≠ some u :=
λ hu, (option.some_ne_none u (hu.symm.trans h))

lemma lookup_ne_none_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  cache.lookup i t ≠ none := λ hu, (option.some_ne_none u (h.symm.trans hu))

/-- Generalized version of `query_cache.extₗ` for when one cache is parameterized by some query
inputs and outputs, handling the cases where indices/inputs differ independently. -/
protected lemma extₗ_induction
  (cache : Π (i : spec.ι), spec.domain i → spec.range i → query_cache spec)
  (cache' : query_cache spec) (i t u) (h₁ : (cache i t u).lookup i t = cache'.lookup i t)
  (h₂ : ∀ t', t ≠ t' → (cache i t u).lookup i t' = cache'.lookup i t')
  (h₃ : ∀ i' t', i ≠ i' → (cache i t u).lookup i' t' = cache'.lookup i' t') :
  cache i t u = cache' :=
begin
  refine query_cache.extₗ (λ i' t', _),
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t',
    { exact ht ▸ h₁ },
    { exact h₂ _ ht } },
  { exact h₃ _ _ hi }
end

end lookup

section mem

/-- `mem_inputs t cache` means that `t` is in the set of inputs that are cached in `cache`.
We make the index implicit to enable the use of the notation `t ∈ᵢ cache` and `t ∉ᵢ cache`. -/
@[derive decidable] def mem_inputs {i : spec.ι} (t : spec.domain i) (cache : query_cache spec) :=
(sigma.mk i t) ∈ cache.cached_inputs

-- Because of the implicit oracle index parameter, we can't just use `has_mem`.
infix ` ∈ᵢ ` : 50 := query_cache.mem_inputs
notation t ` ∉ᵢ `:50 cache:50 := ¬ t ∈ᵢ cache

lemma mem_iff_mem_cached_inputs (i t) :
  t ∈ᵢ cache ↔ (sigma.mk i t) ∈ cache.cached_inputs := iff.rfl

lemma mem_iff_mem_cached_inputs' (x : Σ i : spec.ι, spec.domain i) :
  x.2 ∈ᵢ cache ↔ x ∈ cache.cached_inputs := by cases x; refl

/-- An input is cached in `cache` iff `lookup` returns a non-`none` result. -/
lemma mem_iff_exists_lookup_eq_some (i t) : t ∈ᵢ cache ↔ ∃ u, cache.lookup i t = some u :=
by rw [mem_iff_mem_cached_inputs, mem_cached_inputs, ← option.is_some_iff_exists, ne.def,
  ← option.is_none_iff_eq_none, ← not_iff_not, option.not_is_some_iff_eq_none,
  option.is_none_iff_eq_none, not_not, apply_eq_lookup]

lemma mem_iff_lookup_ne_none (i t) : t ∈ᵢ cache ↔ cache.lookup i t ≠ none :=
by simp [option.eq_none_iff_forall_not_mem, mem_iff_exists_lookup_eq_some]

lemma mem_of_lookup_eq_some {i t u} (h : cache.lookup i t = some u) :
  t ∈ᵢ cache := (cache.mem_iff_exists_lookup_eq_some i t).2 ⟨u, h⟩

lemma exists_lookup_eq_some_of_mem {i t} (h : t ∈ᵢ cache) :
  ∃ u, cache.lookup i t = some u := (cache.mem_iff_exists_lookup_eq_some i t).1 h

lemma not_mem_iff_not_mem_cached_inputs (i t) :
  t ∉ᵢ cache ↔ (sigma.mk i t) ∉ cache.cached_inputs := iff.rfl

@[simp] lemma lookup_eq_none_iff_not_mem (i t) : cache.lookup i t = none ↔ t ∉ᵢ cache :=
by simp [option.eq_none_iff_forall_not_mem, mem_iff_exists_lookup_eq_some]

@[simp] lemma none_eq_lookup_iff_not_mem (i t) : none = cache.lookup i t ↔ t ∉ᵢ cache :=
by rw [eq_comm, lookup_eq_none_iff_not_mem]

lemma not_mem_iff_lookup_eq_none (i t) : t ∉ᵢ cache ↔ cache.lookup i t = none :=
(lookup_eq_none_iff_not_mem cache i t).symm

lemma not_mem_of_lookup_eq_none {i t} (h : cache.lookup i t = none) : t ∉ᵢ cache :=
(not_mem_iff_lookup_eq_none cache i t).2 h

@[simp] lemma lookup_eq_none_of_not_mem {i t} (h : t ∉ᵢ cache) : cache.lookup i t = none :=
(not_mem_iff_lookup_eq_none cache i t).1 h

lemma lookup_ne_some_of_not_mem {i t} (h : t ∉ᵢ cache) (u) : cache.lookup i t ≠ some u :=
begin
  rw [mem_iff_exists_lookup_eq_some, not_exists] at h,
  exact h u,
end

lemma not_mem_of_not_mem_of_lookup_eq {cache cache' : query_cache spec} {i t}
  (h : t ∉ᵢ cache) (h' : cache.lookup i t = cache'.lookup i t) : t ∉ᵢ cache' :=
begin
  rw [not_mem_iff_lookup_eq_none] at h ⊢,
  exact h'.symm.trans h
end

lemma mem_of_mem_of_lookup_eq {cache cache' : query_cache spec} {i t}
  (h : t ∈ᵢ cache) (h' : cache.lookup i t = cache'.lookup i t) : t ∈ᵢ cache' :=
begin
  rw [mem_iff_exists_lookup_eq_some] at h ⊢,
  simp [← h', h],
end

lemma not_mem_of_cached_inputs_subset {cache cache' : query_cache spec} {i} {t : spec.domain i}
  (h : t ∉ᵢ cache') (h' : cache.cached_inputs ⊆ cache'.cached_inputs) : t ∉ᵢ cache :=
begin
  rw [mem_iff_mem_cached_inputs] at h ⊢,
  exact λ h'', h (h' h''),
end

lemma mem_of_cached_inputs_subset {cache cache' : query_cache spec} {i} {t : spec.domain i}
  (h : t ∈ᵢ cache) (h' : cache.cached_inputs ⊆ cache'.cached_inputs) : t ∈ᵢ cache' :=
begin
  rw [mem_iff_mem_cached_inputs] at h ⊢,
  exact h' h,
end

@[simp] lemma some_get_or_else_lookup_of_mem {i t u} (h : t ∈ᵢ cache) :
  some ((cache.lookup i t).get_or_else u) = cache.lookup i t :=
let ⟨u, hu⟩ := exists_lookup_eq_some_of_mem _ h in by simp [hu]

end mem

section empty

variables (i : spec.ι) (t : spec.domain i)

/-- Empty cache has no cached values, so `cache_fn` always returns `none`. -/
def empty (spec : oracle_spec) : query_cache spec :=
{ cache_fn := λ _ _, none,
  cached_inputs := ∅,
  mem_cached_inputs := by simp }

instance : has_emptyc (query_cache spec) := ⟨empty spec⟩

instance : inhabited (query_cache spec) := ⟨∅⟩

@[simp] lemma cached_inputs_empty : cached_inputs (∅ : query_cache spec) = ∅ := rfl

@[simp] lemma lookup_empty : lookup ∅ i t = none := rfl

lemma lookup_empty_ne_some (u : spec.range i) : lookup ∅ i t ≠ some u := by simp

@[simp] lemma not_mem_empty : t ∉ᵢ (∅ : query_cache spec) := by simp [mem_iff_mem_cached_inputs]

@[simp] lemma eq_empty_iff_forall_not_mem : cache = ∅ ↔ ∀ i (t : spec.domain i), t ∉ᵢ cache :=
by simp [query_cache.ext_iffₗ]

lemma eq_empty_iff_forall_eq_none : cache = ∅ ↔ ∀ i t, cache.lookup i t = none := by simp

lemma ne_empty_iff_exists_mem : cache ≠ ∅ ↔ ∃ i (t : spec.domain i), t ∈ᵢ cache := by simp

lemma ne_empty_iff_exists_eq_some : cache ≠ ∅ ↔ ∃ i t u, cache.lookup i t = some u :=
by simp only [ne_empty_iff_exists_mem, mem_iff_exists_lookup_eq_some]

end empty

section cache_query

/-- Add a new value to the cache, erasing any old value if it already exists. -/
def cache_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) (cache : query_cache spec) :
  query_cache spec :=
{ cache_fn := λ i' t', if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t',
  cached_inputs := insert ⟨i, t⟩ cache.cached_inputs,
  mem_cached_inputs := λ x, begin
    obtain ⟨i', t'⟩ := x,
    by_cases hi : i = i',
    { induction hi,
      by_cases ht : t = t',
      { simp [ht] },
      { simp [ht, ne.symm ht, mem_iff_mem_cached_inputs] } },
    { simp [hi, ne.symm hi, mem_iff_mem_cached_inputs] }
  end }

notation `[` i `,` t `↦` u `;` cache `]` := cache_query i t u cache

lemma lookup_cache_query (i t u i' t') :
  [i, t ↦ u; cache].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else cache.lookup i' t') else cache.lookup i' t' := rfl

@[simp] lemma lookup_cache_query_same_index (i t u t') :
  [i, t ↦ u; cache].lookup i t' = if t = t' then some u else cache.lookup i t' :=
by simp [lookup_cache_query]

@[simp] lemma lookup_cache_query_diff_index {i i'} (hi : i ≠ i') (t u t') :
  [i, t ↦ u; cache].lookup i' t' = cache.lookup i' t' := by simp [lookup_cache_query, hi]

lemma lookup_cache_query_same_input (i t u) :
  [i, t ↦ u; cache].lookup i t = some u := by simp

@[simp] lemma lookup_cache_query_diff_input (i) {t t'} (ht : t ≠ t') (u) :
  [i, t ↦ u; cache].lookup i t' = cache.lookup i t' := by simp [ht]

@[simp] lemma cached_inputs_cache_query (i t u) :
  [i, t ↦ u; cache].cached_inputs = insert ⟨i, t⟩ cache.cached_inputs := rfl

@[simp] lemma cache_query_ne_empty (i t u) : [i, t ↦ u; cache] ≠ ∅ :=
ne_of_lookup_ne _ _ i t (by simp)

@[simp] lemma mem_cache_query_iff (i t u i') (t' : spec.domain i') :
  t' ∈ᵢ [i, t ↦ u; cache] ↔ t' ∈ᵢ cache ∨ (∃ (h : i = i'), h.rec t = t') :=
begin
  rw [mem_iff_lookup_ne_none],
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t'; simp [ht] },
  { simp [hi] }
end

lemma mem_cache_query_same_index_iff (i t u) (t' : spec.domain i) :
  t' ∈ᵢ [i, t ↦ u; cache] ↔ t' ∈ᵢ cache ∨ t = t' := by simp

lemma mem_cache_query_diff_index_iff {i i'} (hi : i ≠ i') (t u) (t' : spec.domain i') :
  t' ∈ᵢ [i, t ↦ u; cache] ↔ t' ∈ᵢ cache := by simp [hi]

lemma mem_cache_query_same_input (i t u) :
  t ∈ᵢ [i, t ↦ u; cache] := by simp

lemma mem_cache_query_diff_input_iff (i) {t t'} (ht : t ≠ t') (u) :
  t' ∈ᵢ [i, t ↦ u; cache] ↔ t' ∈ᵢ cache := by simp [ht]

lemma cache_query_inj_of_not_mem {cache cache' : query_cache spec}
  {i t} (h : t ∉ᵢ cache) (h' : t ∉ᵢ cache') (u) :
  [i, t ↦ u; cache] = [i, t ↦ u; cache'] ↔ cache = cache' :=
begin
  simp only [query_cache.ext_iffₗ],
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

lemma cache_query_eq_cache_query_iff_of_same_cache (i t u u') :
  [i, t ↦ u; cache] = [i, t ↦ u'; cache] ↔ u = u' :=
⟨λ h, by simpa only [lookup_cache_query_same_input] using
  ((query_cache.ext_iffₗ _ _).1 h) i t , λ h, by rw [h]⟩

@[simp] lemma cache_query_eq_self_iff (i t u) :
  [i, t ↦ u; cache] = cache ↔ cache.lookup i t = some u :=
⟨λ h, by rw [← h, lookup_cache_query_same_input], λ h,
  query_cache.extₗ_induction (λ i t u, [i, t ↦ u; cache]) cache
  i t u (by simp [h.symm]) (λ t' ht', by simp [ht']) (λ i' t' hi', by simp [hi'])⟩

end cache_query

section drop_query

/-- Set the cached value at the given input back to `none`. -/
def drop_query (i : spec.ι) (t : spec.domain i) (cache : query_cache spec) :
  query_cache spec :=
{ cache_fn := λ i' t', if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t',
  cached_inputs := cache.cached_inputs \ {⟨i, t⟩} ,
  mem_cached_inputs := λ x, begin
    obtain ⟨i', t'⟩ := x,
    by_cases hi : i = i',
    { induction hi,
      by_cases ht : t = t',
      { simp [ht] },
      { simp [ht, ne.symm ht, mem_cached_inputs] } },
    { simp [hi, ne.symm hi, mem_cached_inputs] }
  end }

lemma lookup_drop_query (i t i' t') :
  (cache.drop_query i t).lookup i' t' = if h : i = i' then
    (if h.rec t = t' then none else cache.lookup i' t') else cache.lookup i' t' := rfl

@[simp] lemma lookup_drop_query_same_index (i t t') :
  (cache.drop_query i t).lookup i t' = if t = t' then none else cache.lookup i t' :=
by simp [lookup_drop_query]

@[simp] lemma lookup_drop_query_diff_index {i i'} (hi : i ≠ i') (t t') :
  (cache.drop_query i t).lookup i' t' = cache.lookup i' t' := by simp [lookup_drop_query, hi]

lemma lookup_drop_query_same_input (i t) : (cache.drop_query i t).lookup i t = none := by simp

lemma lookup_drop_query_diff_input (i) {t t'} (ht : t ≠ t'):
  (cache.drop_query i t).lookup i t' = cache.lookup i t' := by simp [ht]

@[simp] lemma drop_query_of_not_mem {i t} (h : t ∉ᵢ cache) : cache.drop_query i t = cache :=
query_cache.extₗ_induction (λ i t u, cache.drop_query i t)
  cache i t default (by simp [h]) (λ t ht, by simp [ht]) (λ i t hi, by simp [hi])

@[simp] lemma mem_drop_query_iff (i t i') (t' : spec.domain i') :
  t' ∈ᵢ (cache.drop_query i t) ↔ t' ∈ᵢ cache ∧ (if h : i = i' then h.rec t ≠ t' else true) :=
begin
  rw [mem_iff_lookup_ne_none],
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t'; simp [ht] },
  { simp [hi] }
end

lemma mem_drop_query_same_index_iff (i t) (t' : spec.domain i) :
  t' ∈ᵢ (cache.drop_query i t) ↔ t' ∈ᵢ cache ∧ t ≠ t' := by simp

lemma mem_drop_query_diff_index_iff {i i'} (hi : i ≠ i') (t) (t' : spec.domain i') :
  t' ∈ᵢ (cache.drop_query i t) ↔ t' ∈ᵢ cache := by simp [hi]

lemma not_mem_drop_query_same_input (i t) : t ∉ᵢ (cache.drop_query i t) := by simp

lemma mem_drop_query_diff_input_iff (i) {t t'} (ht : t ≠ t') :
  t' ∈ᵢ (cache.drop_query i t) ↔ t' ∈ᵢ cache := by simp [ht]

@[simp] lemma drop_query_empty (i : spec.ι) (t) : drop_query i t ∅ = ∅ := by simp

end drop_query

section drop_query_cache_query

/-- Adding a query to the cache and then dropping a query commutes to dropping and then adding,
unless the inputs being cached are the same as the one being dropped. -/
@[simp] lemma drop_query_cache_query (i t u i' t') :
  [i, t ↦ u; cache].drop_query i' t' = if ∃ (h : i = i'), h.rec t = t'
    then cache.drop_query i' t' else [i, t ↦ u; cache.drop_query i' t'] :=
begin
  refine query_cache.extₗ (λ i'' t'', _),
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

lemma drop_query_cache_query_same_index (i t u t') : [i, t ↦ u; cache].drop_query i t' =
  if t = t' then cache.drop_query i t' else [i, t ↦ u; cache.drop_query i t'] := by simp

lemma drop_query_cache_query_diff_index {i i'} (h : i ≠ i') (t u t') :
  [i, t ↦ u; cache].drop_query i' t' = [i, t ↦ u; cache.drop_query i' t'] := by simp [h]

lemma drop_query_cache_query_same_input (i t u) :
  [i, t ↦ u; cache].drop_query i t = cache.drop_query i t := by simp

lemma drop_query_cache_query_diff_input (i) {t t'} (h : t ≠ t') (u) :
  [i, t ↦ u; cache].drop_query i t' = [i, t ↦ u; cache.drop_query i t'] := by simp [h]

end drop_query_cache_query

section cache_query_drop_query

lemma cache_query_drop_query (i t u i' t') :
  [i, t ↦ u; cache.drop_query i' t'] = if ∃ (h : i = i'), h.rec t = t'
    then [i, t ↦ u; cache] else [i, t ↦ u; cache].drop_query i' t' :=
begin
  refine query_cache.extₗ (λ i'' t'', _),
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

lemma cache_query_drop_query_same_index (i t u t') :
  [i, t ↦ u; cache.drop_query i t'] = if t = t' then [i, t ↦ u; cache]
    else [i, t ↦ u; cache].drop_query i t' :=
by simp only [cache_query_drop_query, eq_self_iff_true, exists_true_left]

/-- Adding a value to a cache after removing a value for the same inputs is the same as just
caching it into the original cache, since adding new values replaces old ones. -/
@[simp] lemma cache_query_drop_query_same_input (i t u) :
  [i, t ↦ u; cache.drop_query i t] = [i, t ↦ u; cache] :=
by simp only [cache_query_drop_query, eq_self_iff_true, exists_true_left, if_true]

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

-- variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma singleton.def (i t) (u : spec.range i) : [i, t ↦ u] = [i, t ↦ u; ∅] := rfl

lemma lookup_singleton (i : spec.ι) (t u i' t') :
  [i, t ↦ u].lookup i' t' = if h : i = i' then
    (if h.rec t = t' then some (h.rec u) else none) else none := rfl

@[simp] lemma lookup_singleton_same_index (i : spec.ι) (t u t') :
  [i, t ↦ u].lookup i t' = if t = t' then some u else none := by simp [lookup_singleton]

@[simp] lemma lookup_singleton_diff_index {i i' : spec.ι} (hi : i ≠ i') (t u t') :
  [i, t ↦ u].lookup i' t' = none := by simp [lookup_singleton, hi]

lemma lookup_singleton_same_input (i : spec.ι) (t u) :
  [i, t ↦ u].lookup i t = some u := by simp

@[simp] lemma lookup_singleton_diff_input (i : spec.ι) {t t'} (ht : t ≠ t') (u) :
  [i, t ↦ u].lookup i t' = none := by simp [ht]

@[simp] lemma cached_inputs_singleton (i : spec.ι) (t u) :
  [i, t ↦ u].cached_inputs = {⟨i, t⟩} := rfl

lemma lookup_singleton_eq_some_iff (i : spec.ι) (t u i' t' u') :
  [i, t ↦ u].lookup i' t' = some u' ↔
    ∃ (h : i = i'), h.rec t = t' ∧ h.rec u = u' :=
by simp [lookup_singleton, dite_eq_iff, ite_eq_iff]

lemma lookup_singleton_eq_some_iff_same_index (i : spec.ι) (t u t' u') :
  [i, t ↦ u].lookup i t' = some u' ↔ t = t' ∧ u = u' :=
by simp [lookup_singleton_eq_some_iff, ite_eq_iff]

lemma lookup_singleton_eq_some_iff_same_input (i : spec.ι) (t u u') :
  [i, t ↦ u].lookup i t = some u' ↔ u = u' := by simp

lemma singleton_ne_empty (i : spec.ι) (t u) : [i, t ↦ u] ≠ ∅ := cache_query_ne_empty ∅ i t u

@[simp] lemma mem_singleton_iff (i : spec.ι) (t u i' t') :
  t' ∈ᵢ [i, t ↦ u] ↔ ∃ (h : i = i'), h.rec t = t' := by simp [singleton.def]

lemma mem_singleton_iff_same_index (i : spec.ι) (t u t') :
  t' ∈ᵢ [i, t ↦ u] ↔ t = t' := by simp

lemma not_mem_singleton_diff_index {i i' : spec.ι} (hi : i ≠ i') (t u) (t' : spec.domain i') :
  t' ∉ᵢ [i, t ↦ u] := by simp [hi]

lemma mem_singleton_same_input (i : spec.ι) (t u) : t ∈ᵢ [i, t ↦ u] := by simp

lemma not_mem_singleton_diff_input (i : spec.ι) {t t'} (ht : t ≠ t') (u) :
  t' ∉ᵢ [i, t ↦ u] := by simp [ht]

@[simp] lemma drop_query_singleton (i : spec.ι) (t u i' t') :
  [i, t ↦ u].drop_query i' t' = if ∃ (h : i = i'), h.rec t = t' then ∅ else [i, t ↦ u] :=
by simp [singleton.def]

lemma drop_query_singleton_same_index (i : spec.ι) (t u t') :
  [i, t ↦ u].drop_query i t' = if t = t' then ∅ else [i, t ↦ u] := by simp

lemma drop_query_singleton_diff_index {i i' : spec.ι} (hi : i ≠ i') (t u t') :
  [i, t ↦ u].drop_query i' t' = [i, t ↦ u] := by simp [hi]

lemma drop_query_singleton_same_input (i : spec.ι) (t u) :
  [i, t ↦ u].drop_query i t = ∅ := by simp

lemma drop_query_singleton_diff_input (i : spec.ι) {t t'} (ht : t ≠ t') (u) :
  [i, t ↦ u].drop_query i t' = [i, t ↦ u] := by simp [ht]

lemma lookup_cache_query_eq_lookup_singleton (i : spec.ι) (t u) {i' t'} (h : t' ∉ᵢ cache) :
  [i, t ↦ u; cache].lookup i' t' = [i, t ↦ u].lookup i' t' :=
begin
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t',
    { simp [ht] },
    { simp [ht, h] } },
  { simp [hi, h] }
end

end singleton

end query_cache

end oracle_spec
