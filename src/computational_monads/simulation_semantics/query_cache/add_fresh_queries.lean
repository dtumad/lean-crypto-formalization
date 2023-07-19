/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.query_cache.order

/-!
# Merging Fresh Values Into a Cache

This file defines a function `cache.add_fresh_queries cache'` that adds values from `cache'` to
`cache`, assuming the value is fresh, leaving other values unchanged.

If the two `query_cache`s are disjoint this acts like a sup operation, but in general doesn't
satisfy the criteria for being a `semilattice`.
-/

namespace query_cache

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Add queries in `s'` to `s`, for any query that is fresh to `s`.
If the query isn't fresh preserve the value cached in `s'`.
This behaves like a `⊔` operation if the caches have disjoint `cached_inputs` sets,
but doesn't in general, so we choose not to implement a `has_sup` typeclass instance. -/
def add_fresh_queries (cache cache' : query_cache spec) : query_cache spec :=
{ cache_fn := λ i t, if t ∈ᵢ cache then cache.lookup i t else cache'.lookup i t,
  cached_inputs := cache.cached_inputs ∪ cache'.cached_inputs,
  mem_cached_inputs := λ x, by split_ifs with hx; simp [hx, ← mem_iff_mem_cached_inputs'] }

variables (cache cache' : query_cache spec)

@[simp] lemma cached_inputs_add_fresh_queries : (cache.add_fresh_queries cache').cached_inputs =
  cache.cached_inputs ∪ cache'.cached_inputs := rfl

@[simp] lemma lookup_add_fresh_queries (i t) : (cache.add_fresh_queries cache').lookup i t =
  if t ∈ᵢ cache then cache.lookup i t else cache'.lookup i t := rfl

lemma lookup_add_fresh_queries_of_mem {i t} (h : t ∈ᵢ cache) :
  (cache.add_fresh_queries cache').lookup i t = cache.lookup i t := by simp [h]

lemma lookup_add_fresh_queries_of_not_mem {i t} (h : t ∉ᵢ cache) :
  (cache.add_fresh_queries cache').lookup i t = cache'.lookup i t := by simp [h]

@[simp] lemma not_mem_add_fresh_queries_iff (i : spec.ι) (t : spec.domain i) :
  t ∉ᵢ (cache.add_fresh_queries cache') ↔ t ∉ᵢ cache ∧ t ∉ᵢ cache' :=
by simp [not_mem_iff_not_mem_cached_inputs, not_or_distrib]

@[simp] lemma mem_add_fresh_queries_iff (i : spec.ι) (t : spec.domain i) :
  t ∈ᵢ (cache.add_fresh_queries cache') ↔ t ∈ᵢ cache ∨ t ∈ᵢ cache' :=
by simp [mem_iff_mem_cached_inputs]

@[simp] lemma add_fresh_queries_empty (cache : query_cache spec) :
  cache.add_fresh_queries ∅ = cache :=
by simp [query_cache.ext_iffₗ]

@[simp] lemma empty_add_fresh_queries (cache : query_cache spec) :
  add_fresh_queries ∅ cache = cache :=
by simp [query_cache.ext_iffₗ]

@[simp] lemma add_fresh_queries_eq_self_iff (cache cache' : query_cache spec) :
  cache.add_fresh_queries cache' = cache ↔ cache'.cached_inputs ⊆ cache.cached_inputs :=
begin
  refine ⟨λ h x hx, _, λ h, _⟩,
  { rw [← h, cached_inputs_add_fresh_queries, finset.mem_union],
    exact or.inr hx },
  { refine query_cache.extₗ (λ i t, ite_eq_left_iff.2 (λ ht, _)),
    exact (lookup_eq_none_of_not_mem _ (not_mem_of_cached_inputs_subset ht h)).trans
      (lookup_eq_none_of_not_mem _ ht).symm }
end

lemma add_fresh_queries_eq_self_of_le {cache cache' : query_cache spec} (h : cache' ≤ cache) :
  cache.add_fresh_queries cache' = cache :=
(add_fresh_queries_eq_self_iff cache cache').2 (cached_inputs_subset_cached_inputs_of_le h)

end query_cache