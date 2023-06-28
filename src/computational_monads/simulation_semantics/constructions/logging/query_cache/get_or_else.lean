/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.query_cache.order
import computational_monads.distribution_semantics.ite
import computational_monads.distribution_semantics.prod

/-!
# Looking Up Cache Values with Fallback

This file defines a function `cache.get_or_else i t ou` that checks for a cached value of `i, t`,
and if not found runs `ou` to get a new result rather than returning `none`.
-/

namespace query_cache

open oracle_spec oracle_comp

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Lookup the given value in the cache and return it without changing the cache,
using `ou` as a fallback instead if the query is fresh to the cache. -/
def get_or_else (cache : query_cache spec) (i : spec.ι) (t : spec.domain i)
  (ou : oracle_comp spec' (spec.range i)) : oracle_comp spec' (spec.range i × query_cache spec) :=
match cache.lookup i t with
| none := do {u ← ou, return (u, [i, t ↦ u; cache])}
| (some u) := return (u, cache)
end

variables (cache cache' : query_cache spec)

section ite

variables (i : spec.ι) (t : spec.domain i) (ou : oracle_comp spec' (spec.range i))

lemma get_or_else_eq_ite : cache.get_or_else i t ou =
  if cache.is_fresh i t then ou >>= λ u, return (u, [i, t ↦ u; cache])
    else return ((cache.lookup i t).get_or_else default, cache) :=
begin
  split_ifs with h,
  { simp [get_or_else, lookup_eq_none_of_is_fresh _ h] },
  { rw [not_is_fresh_iff_exists_lookup_eq_some] at h,
    obtain ⟨u, hu⟩ := h,
    simp [get_or_else, hu] }
end

lemma support_get_or_else : (cache.get_or_else i t ou).support =
  if cache.is_fresh i t then (λ u, (u, [i, t ↦ u; cache])) '' ou.support else
    {((cache.lookup i t).get_or_else default, cache)} :=
by simp [get_or_else_eq_ite]

lemma mem_support_get_or_else_iff (x : spec.range i × query_cache spec) :
  x ∈ (cache.get_or_else i t ou).support ↔
    if cache.is_fresh i t then x.1 ∈ ou.support ∧ [i, t ↦ x.1; cache] = x.2 else
      cache.lookup i t = some x.1 ∧ x.2 = cache :=
begin
  split_ifs with h,
  { simp [get_or_else_eq_ite, h],
    refine ⟨λ h', _, λ h', _⟩,
    { obtain ⟨u, hu⟩ := h',
      rw [prod.eq_iff_fst_eq_snd_eq] at hu,
      exact ⟨hu.2.1 ▸ hu.1, hu.2.1 ▸ hu.2.2⟩ },
    { exact ⟨x.1, h'.1, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, h'.2⟩⟩ } },
  { obtain ⟨u, hu⟩ := lookup_eq_some_of_is_cached _ (is_cached_of_not_is_fresh _ h),
    simp [get_or_else_eq_ite, h, prod.eq_iff_fst_eq_snd_eq, hu, eq_comm] }
end

lemma eval_dist_get_or_else : ⁅cache.get_or_else i t ou⁆ =
  if cache.is_fresh i t then ⁅ou⁆.map (λ u, (u, [i, t ↦ u; cache]))
    else pmf.pure ((cache.lookup i t).get_or_else default, cache) :=
by simp [get_or_else_eq_ite]

lemma prob_output_get_or_else (x) : ⁅= x | cache.get_or_else i t ou⁆ =
  if cache.is_fresh i t then ⁅= x | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆
    else ⁅= x | return' !spec'! ((cache.lookup i t).get_or_else default, cache)⁆ :=
by simp [get_or_else_eq_ite]

lemma prob_event_get_or_else (e) : ⁅e | cache.get_or_else i t ou⁆ =
  if cache.is_fresh i t then ⁅e | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆
    else ⁅e | return' !spec! ((cache.lookup i t).get_or_else default, cache)⁆ :=
by simp [get_or_else_eq_ite]

lemma get_or_else_dist_equiv : cache.get_or_else i t ou ≃ₚ
  if cache.is_fresh i t then ou >>= λ u, return (u, [i, t ↦ u; cache]) else
    return ((cache.lookup i t).get_or_else default, cache) :=
by rw [get_or_else_eq_ite]

-- lemma get_or_else_dist_equiv_get_or_else

end ite

section is_fresh

variables {i : spec.ι} {t : spec.domain i} (ou : oracle_comp spec' (spec.range i))

@[simp] lemma get_or_else_of_is_fresh (h : cache.is_fresh i t) :
  cache.get_or_else i t ou = ou >>= λ u, return (u, [i, t ↦ u; cache]) :=
by simp [get_or_else, h]

lemma support_get_or_else_of_is_fresh (h : cache.is_fresh i t) :
  (cache.get_or_else i t ou).support = (λ u, (u, [i, t ↦ u; cache])) '' ou.support :=
by simp [h]

lemma mem_support_get_or_else_iff_of_is_fresh (h : cache.is_fresh i t)
  (x : spec.range i × query_cache spec) : x ∈ (cache.get_or_else i t ou).support ↔
    x.1 ∈ ou.support ∧ [i, t ↦ x.1; cache] = x.2 :=
by simp only [mem_support_get_or_else_iff, h, if_true]

lemma eval_dist_get_or_else_of_is_fresh (h : cache.is_fresh i t) :
  ⁅cache.get_or_else i t ou⁆ = ⁅ou⁆.map (λ u, (u, [i, t ↦ u; cache])) :=
by simp [h]

lemma prob_output_get_or_else_of_is_fresh (h : cache.is_fresh i t) (x) :
  ⁅= x | cache.get_or_else i t ou⁆ = ⁅= x | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆ :=
by simp [h]

lemma prob_event_get_or_else_of_is_fresh (h : cache.is_fresh i t) (e) :
  ⁅e | cache.get_or_else i t ou⁆ = ⁅e | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆ :=
by simp [h]

lemma get_or_else_dist_equiv_of_is_fresh (h : cache.is_fresh i t) :
  cache.get_or_else i t ou ≃ₚ ou >>= λ u, return (u, [i, t ↦ u; cache]) :=
by rw [get_or_else_of_is_fresh _ _ h]

end is_fresh

section is_cached

variables {i : spec.ι} {t : spec.domain i} (ou : oracle_comp spec' (spec.range i))

@[simp] lemma get_or_else_of_is_cached (h : cache.is_cached i t) :
  cache.get_or_else i t ou = return ((cache.lookup i t).get_or_else default, cache) :=
by simp only [get_or_else_eq_ite, ← not_is_cached_iff_is_fresh, h, not_true, if_false]

lemma support_get_or_else_of_is_cached (h : cache.is_cached i t) :
  (cache.get_or_else i t ou).support = {((cache.lookup i t).get_or_else default, cache)} :=
by simp [h]

lemma mem_support_get_or_else_iff_of_is_cached (h : cache.is_cached i t)
  (x : spec.range i × query_cache spec) : x ∈ (cache.get_or_else i t ou).support ↔
    cache.lookup i t = some x.1 ∧ x.2 = cache :=
by simp only [(not_is_fresh_of_is_cached _ h), mem_support_get_or_else_iff, if_false]

lemma eval_dist_get_or_else_of_is_cached (h : cache.is_cached i t) :
  ⁅cache.get_or_else i t ou⁆ = pmf.pure ((cache.lookup i t).get_or_else default, cache) :=
by simp [h]

lemma prob_output_get_or_else_of_is_cached (h : cache.is_cached i t) (x) :
  ⁅= x | cache.get_or_else i t ou⁆ =
    ⁅= x | return' !spec'! ((cache.lookup i t).get_or_else default, cache)⁆ :=
by simp [h]

lemma prob_event_get_or_else_of_is_cached (h : cache.is_cached i t) (e) :
  ⁅e | cache.get_or_else i t ou⁆ =
    ⁅e | return' !spec! ((cache.lookup i t).get_or_else default, cache)⁆ :=
by simp [h]

lemma get_or_else_dist_equiv_of_is_cached (h : cache.is_cached i t) :
  cache.get_or_else i t ou ≃ₚ return' !spec! ((cache.lookup i t).get_or_else default, cache) :=
by simp [h]

end is_cached

section lookup_eq_some

variables {i : spec.ι} {t : spec.domain i} {u : spec.range i}
  (ou : oracle_comp spec' (spec.range i))

lemma get_or_else_of_lookup_eq_some (h : cache.lookup i t = some u) :
  cache.get_or_else i t ou = return (u, cache) :=
by simp [get_or_else, h]

lemma support_get_or_else_of_lookup_eq_some (h : cache.lookup i t = some u) :
  (cache.get_or_else i t ou).support = {(u, cache)} :=
by simp [get_or_else_of_lookup_eq_some _ _ h]

lemma eval_dist_get_or_else_of_lookup_eq_some (h : cache.lookup i t = some u) :
  ⁅cache.get_or_else i t ou⁆ = pmf.pure (u, cache) :=
by simp [get_or_else_of_lookup_eq_some _ _ h]

lemma prob_output_get_or_else_of_lookup_eq_some (h : cache.lookup i t = some u) (x) :
  ⁅= x | cache.get_or_else i t ou⁆ = ⁅= x | return' !spec'! (u, cache)⁆ :=
by simp [get_or_else_of_lookup_eq_some _ _ h]

lemma prob_event_get_or_else_of_lookup_eq_some (h : cache.lookup i t = some u) (e) :
  ⁅e | cache.get_or_else i t ou⁆ = ⁅e | return' !spec! (u, cache)⁆ :=
by simp [get_or_else_of_lookup_eq_some _ _ h]

lemma get_or_else_dist_equiv_of_lookup_eq_some (h : cache.lookup i t = some u) :
  cache.get_or_else i t ou ≃ₚ return' !spec! (u, cache) :=
by simp [get_or_else_of_lookup_eq_some _ _ h]

end lookup_eq_some

section empty

variables (i : spec.ι) (t : spec.domain i) (ou : oracle_comp spec' (spec.range i))

@[simp] lemma get_or_else_init : get_or_else ∅ i t ou = do {u ← ou, return (u, [i, t ↦ u])} :=
by simp [is_fresh_init i t, singleton.def]

end empty

section lookup

variables {i : spec.ι} {t : spec.domain i} {ou : oracle_comp spec' (spec.range i)}
  (x : spec.range i × query_cache spec)

lemma lookup_snd_eq_of_mem_support_get_or_else (i' : spec.ι) (t' : spec.domain i')
  (h : x ∈ (cache.get_or_else i t ou).support) : x.2.lookup i' t' =
    if h : i = i' then (if h.rec t = t' then some (h.rec x.1)
      else cache.lookup i' t') else cache.lookup i' t' :=
begin
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : cache.is_fresh i t,
    { rw [mem_support_get_or_else_iff_of_is_fresh _ _ ht] at h,
      simp [← h.2] },
    { simp [is_cached_of_not_is_fresh _ ht] at h,
      simp [h, is_cached_of_not_is_fresh _ ht],
      split_ifs with htt; simp [htt] } },
  { by_cases ht : cache.is_fresh i t,
    { rw [mem_support_get_or_else_iff_of_is_fresh _ _ ht] at h,
      simp [← h.2, hi] },
    { simp [is_cached_of_not_is_fresh _ ht] at h,
      simp [h, is_cached_of_not_is_fresh _ ht, hi] } }
end

lemma lookup_snd_eq_of_mem_support_get_or_else_same_index (t' : spec.domain i)
  (h : x ∈ (cache.get_or_else i t ou).support) : x.2.lookup i t' =
    if t = t' then some x.1 else cache.lookup i t' :=
by simp [lookup_snd_eq_of_mem_support_get_or_else _ _ _ _ h]

lemma lookup_snd_eq_of_mem_support_get_or_else_diff_index (i' : spec.ι) (t' : spec.domain i')
  (hi : i ≠ i') (h : x ∈ (cache.get_or_else i t ou).support) :
  x.2.lookup i' t' = cache.lookup i' t' :=
by simp [lookup_snd_eq_of_mem_support_get_or_else _ _ _ _ h, hi]

lemma lookup_snd_eq_of_mem_support_get_or_else_same_input
  (h : x ∈ (cache.get_or_else i t ou).support) : x.2.lookup i t = some x.1 :=
by simp [lookup_snd_eq_of_mem_support_get_or_else _ _ _ _ h]

lemma lookup_snd_eq_of_mem_support_get_or_else_diff_input (t' : spec.domain i) (ht : t ≠ t')
  (h : x ∈ (cache.get_or_else i t ou).support) : x.2.lookup i t' = cache.lookup i t' :=
by simp [lookup_snd_eq_of_mem_support_get_or_else _ _ _ _ h, ht]

lemma is_cached_of_mem_support_get_or_else
  (h : x ∈ (cache.get_or_else i t ou).support) : x.2.is_cached i t :=
is_cached_of_lookup_eq_some _ (lookup_snd_eq_of_mem_support_get_or_else_same_input _ _ h)

end lookup

section order

variables {i : spec.ι} {t : spec.domain i} {ou : oracle_comp spec' (spec.range i)}
  (x : spec.range i × query_cache spec)

lemma le_of_mem_support_get_or_else (h : x ∈ (cache.get_or_else i t ou).support) : cache ≤ x.2 :=
begin
  by_cases ht : cache.is_fresh i t,
  { rw [mem_support_get_or_else_iff_of_is_fresh _ _ ht] at h,
    refine h.2 ▸ le_cache_query_self _ _ _ _ },
  { rw [mem_support_get_or_else_iff_of_is_cached _ _ (is_cached_of_not_is_fresh _ ht)] at h,
    refine h.2 ▸ le_rfl }
end

lemma le_of_mem_support_snd_map_get_or_else (cache' : query_cache spec)
  (h : cache' ∈ (prod.snd <$> cache.get_or_else i t ou).support) : cache ≤ cache' :=
let ⟨u, hu⟩ := (mem_support_map_snd_iff _ _).1 h in le_of_mem_support_get_or_else cache _ hu

end order

section fst_map

variables {i : spec.ι} {t : spec.domain i} (ou : oracle_comp spec' (spec.range i))

lemma fst_map_get_or_else_dist_equiv_fst_map_get_or_else
  (h : cache.lookup i t = cache'.lookup i t) :
  prod.fst <$> cache.get_or_else i t ou ≃ₚ prod.fst <$> cache'.get_or_else i t ou :=
begin
  by_cases h' : cache.is_cached i t,
  {
    have : cache'.is_cached i t := sorry,
    simp [h', this, h],
  },
  {
    have h1 : cache.is_fresh i t := sorry,
    have : cache'.is_fresh i t := sorry,
    simp [h, h1, this],
  }
end

end fst_map

section bind_fst_map

variables

variables (i : spec.ι) (t : spec.domain i) (ou : oracle_comp spec' (spec.range i))
  (i' : spec.ι) (t' : spec.domain i') (ou' : oracle_comp spec' (spec.range i'))

theorem get_or_else_bind_fst_map_get_or_else_dist_equiv :
  do {x ← cache.get_or_else i t ou, prod.fst <$> x.2.get_or_else i' t' ou'} ≃ₚ
    if h : i = i' then (if h.rec t = t'
      then (congr_arg spec.range h).rec (prod.fst <$> cache.get_or_else i t ou)
      else prod.fst <$> cache.get_or_else i' t' ou')
      else prod.fst <$> cache.get_or_else i' t' ou' :=
begin
  by_cases hi : i = i',
  {
    induction hi,
    by_cases ht : t = t',
    {
      simp [ht],
      calc (cache.get_or_else i t' ou >>= λ x, prod.fst <$> x.snd.get_or_else i t' ou') ≃ₚ
        (cache.get_or_else i t' ou >>= λ x, prod.fst <$> return x) : begin
          refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, _),
          have := lookup_snd_eq_of_mem_support_get_or_else_same_input _ _ hx,
          have := get_or_else_dist_equiv_of_lookup_eq_some _ ou' this,
          rw [prod.mk.eta] at this,
          refine map_dist_equiv_of_dist_equiv rfl (this.trans ((return_dist_equiv_return_iff _ _ _ _).2 rfl)),
        end
        ... ≃ₚ prod.fst <$> (cache.get_or_else i t' ou >>= return) : by push_map_dist_equiv
        ... ≃ₚ prod.fst <$> cache.get_or_else i t' ou :
          map_dist_equiv_of_dist_equiv rfl (by pairwise_dist_equiv)
    },
    {
      simp [ht],
      refine bind_dist_equiv_right _ _ (default, cache) (λ x hx, _),
      -- refine map_dist_equiv_of_dist_equiv rfl _,
      simp,
      have := lookup_snd_eq_of_mem_support_get_or_else_diff_input _ _ _ ht hx,
      sorry,
    }
  },
  {
    simp [hi],
    refine bind_dist_equiv_right _ _ (default, cache) (λ x hx, _),
    refine map_dist_equiv_of_dist_equiv rfl _,
    simp,
    have := lookup_snd_eq_of_mem_support_get_or_else_diff_index _ _ _ t' hi hx,
  }
end


@[simp_dist_equiv]
lemma get_or_else_bind_get_or_else_dist_equiv_same_input (t' : spec.domain i) :
  do {x ← cache.get_or_else i t ou, x.2.get_or_else i t' ou} ≃ₚ
    cache.get_or_else i t' ou :=
begin
  sorry
  -- refine bind_dist_equiv_left _ _ (λ x hx, _),
  -- have := lookup_snd_eq_fst_of_mem_support_get_or_else _ _ hx,
  -- simp [is_cached_of_lookup_eq_some _ this, prod.eq_iff_fst_eq_snd_eq, this]
end

@[simp_dist_equiv]
lemma fst_map_get_or_else_bind_get_or_else_dist_equiv_same_input (t' : spec.domain i) :
  do {x ← cache.get_or_else i t ou, prod.fst <$> x.2.get_or_else i t ou} ≃ₚ
    prod.fst <$> cache.get_or_else i t ou :=
calc do {x ← cache.get_or_else i t ou, prod.fst <$> x.2.get_or_else i t ou} ≃ₚ
  prod.fst <$> (do {x ← cache.get_or_else i t ou, x.2.get_or_else i t ou}) :
    by push_map_dist_equiv
  ... ≃ₚ prod.fst <$> cache.get_or_else i t ou : by pairwise_dist_equiv


end bind_fst_map

end query_cache