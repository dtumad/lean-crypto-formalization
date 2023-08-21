/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_cache.order

/-!
# Removing Cached Values from a Cache

This file defines a `has_sdiff` instance on `query_cache`, where `cache \ cache'` is the result of
dropping any values in `cache` that are also cached in `cache'`.
The removal is independent of the actual values stored in the cache.
-/

namespace query_cache

variables {spec : oracle_spec}

/-- We define a diff operation `cache \ cache'` on `query_cache` by removing any cached elements
in `cache'` from `cache`, leaving everything else unchanged. -/
instance : has_sdiff (query_cache spec) :=
{ sdiff := λ cache cache', {
    cache_fn := λ i t, if t ∉ᵢ cache' then cache.lookup i t else none,
    cached_inputs := cache.cached_inputs \ cache'.cached_inputs,
    mem_cached_inputs := λ x, by simp [and_comm, not_mem_iff_not_mem_cached_inputs] } }

variables (cache cache' : query_cache spec) (i : spec.ι) (t : spec.domain i)

@[simp] lemma cached_inputs_sdiff : (cache \ cache').cached_inputs =
  cache.cached_inputs \ cache'.cached_inputs := rfl

section lookup

@[simp] lemma lookup_sdiff : (cache \ cache').lookup i t =
  if t ∉ᵢ cache' then cache.lookup i t else none := rfl

lemma lookup_sdiff_of_mem {i t} (h : t ∈ᵢ cache') :
  (cache \ cache').lookup i t = none := by simp [h]

lemma lookup_sdiff_of_not_mem {i t} (h : t ∉ᵢ cache') :
  (cache \ cache').lookup i t = cache.lookup i t := by simp [h]

lemma lookup_sdiff_eq_some_iff (u) : (cache \ cache').lookup i t = some u ↔
  t ∉ᵢ cache' ∧ cache.lookup i t = some u :=
by by_cases h : t ∈ᵢ cache'; simp [h]

lemma lookup_sdiff_eq_none_iff : (cache \ cache').lookup i t = none ↔ t ∉ᵢ cache ∨ t ∈ᵢ cache' :=
by rw [lookup_sdiff, ite_eq_right_iff, lookup_eq_none_iff_not_mem,
  imp_iff_not_or, or_comm, not_not]

end lookup

@[simp] lemma mem_sdiff_iff (i : spec.ι) (t : spec.domain i) :
  t ∈ᵢ (cache \ cache') ↔ t ∈ᵢ cache ∧ t ∉ᵢ cache' :=
begin
  simp only [mem_iff_lookup_ne_none, lookup_sdiff],
  simp [and_comm],
end

@[simp] lemma empty_sdiff : ∅ \ cache = ∅ := query_cache.extₗ (λ i t, if_t_t _ _)

@[simp] lemma sdiff_empty : cache \ ∅ = cache := query_cache.extₗ (λ i t, by simp)

@[simp] lemma sdiff_self : cache \ cache = ∅ := query_cache.extₗ (λ i t, by simp)

@[simp] lemma cache_query_sdiff_self (u) : [i, t ↦ u; cache] \ cache =
  if t ∉ᵢ cache  then [i, t ↦ u] else ∅ :=
begin
  refine query_cache.extₗ (λ i' t', _),
  by_cases hit : t ∈ᵢ cache;
  { by_cases hi : i = i',
    { induction hi,
      by_cases ht : t = t',
      { simp [← ht, hit] },
      { simp [ht, hit] } },
    { simp [hi, hit] } },
end

@[simp] lemma sdiff_le_left : cache \ cache' ≤ cache :=
λ i t u hu, ((lookup_sdiff_eq_some_iff _ _ _ _ _).1 hu).2

lemma sdiff_le_right_iff : cache \ cache' ≤ cache' ↔ cache ≤ cache' :=
begin
  sorry,
end

lemma eq_empty_of_le_of_le_diff {cache₀ cache cache' : query_cache spec}
  (hs : cache₀ ≤ cache) (hs' : cache₀ ≤ cache' \ cache) : cache₀ = ∅ :=
begin
  refine eq_bot_iff.2 (λ i t u hu, _),
  specialize hs i t u hu,
  have : t ∈ᵢ cache := mem_of_lookup_eq_some _ hs,
  specialize hs' i t u hu,
  simp [this, lookup_sdiff] at hs',
  refine hs'.elim,
end

lemma drop_query_sdiff (i t u) : (cache \ cache').drop_query i t =
  cache \ [i, t ↦ u; cache'] :=
begin
  refine query_cache.extₗ (λ i' t', _),
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t'; simp [ht] },
  { simp [hi] }
end


lemma cached_inputs_sdiff_subset_cached_inputs_iff_of_le {cache₀ cache cache' : query_cache spec}
  (h₀ : cache₀ ≤ cache') (h' : cache' ≤ cache) :
  (cache \ cache').cached_inputs ⊆ cache₀.cached_inputs ↔ cache = cache' :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    refine le_antisymm _ h',
    refine λ i t u hu, _,
    by_cases ht₀ : t ∈ᵢ cache₀,
    {
      have := mem_of_le_of_mem h₀ ht₀,
      have := lookup_eq_lookup_of_le_of_mem h' this,
      refine this.symm.trans hu
    },
    {
      have := not_mem_of_cached_inputs_subset ht₀ h,
      simp [mem_sdiff_iff, not_and_distrib, (mem_of_lookup_eq_some _ hu)] at this,
      have := lookup_eq_lookup_of_le_of_mem h' this,
      refine this.symm.trans hu,
    }
  },
  {
    rw [h, query_cache.sdiff_self, cached_inputs_empty],
    refine finset.empty_subset _,
  }
end

end query_cache