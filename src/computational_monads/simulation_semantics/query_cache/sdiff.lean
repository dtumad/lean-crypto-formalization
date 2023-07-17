/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.query_cache.order

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
    cache_fn := λ i t, if cache'.is_fresh i t then cache.lookup i t else none,
    cached_inputs := cache.cached_inputs \ cache'.cached_inputs,
    mem_cached_inputs := λ x, by simp [and_comm, is_fresh_iff_not_mem_cached_inputs] } }

variables (cache cache' : query_cache spec) (i : spec.ι) (t : spec.domain i)

section lookup

@[simp] lemma lookup_sdiff : (cache \ cache').lookup i t =
  if cache'.is_fresh i t then cache.lookup i t else none := rfl

lemma lookup_sdiff_eq_some_iff (u) : (cache \ cache').lookup i t = some u ↔
  cache'.is_fresh i t ∧ cache.lookup i t = some u :=
by by_cases h : cache'.is_fresh i t; simp [h]

lemma lookup_sdiff_eq_none_iff : (cache \ cache').lookup i t = none ↔
  cache.is_fresh i t ∨ cache'.is_cached i t :=
by rw [lookup_sdiff, ite_eq_right_iff, lookup_eq_none_iff_is_fresh,
  imp_iff_not_or, not_is_fresh_iff_is_cached, or_comm]

end lookup

@[simp] lemma init_sdiff : ∅ \ cache = ∅ := query_cache.extₗ (λ i t, if_t_t _ _)

@[simp] lemma sdiff_init : cache \ ∅ = cache := query_cache.extₗ (λ i t, by simp)

@[simp] lemma sdiff_self : cache \ cache = ∅ := query_cache.extₗ (λ i t, by simp)

@[simp] lemma sdiff_cache_query (u) : [i, t ↦ u; cache] \ cache =
  if cache.is_fresh i t then [i, t ↦ u] else ∅ :=
begin
  refine query_cache.extₗ (λ i' t', _),
  by_cases hit : cache.is_fresh i t;
  { by_cases hi : i = i',
    { induction hi,
      by_cases ht : t = t',
      { simp [← ht, hit] },
      { simp [ht, hit] } },
    { simp [hi, hit] } },
end

lemma sdiff_le_fst : cache \ cache' ≤ cache :=
begin
  refine λ i t u hu, _,
  rw [lookup_sdiff_eq_some_iff] at hu,
  exact hu.2,
end

end query_cache