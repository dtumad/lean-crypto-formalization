/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_cache.order
import computational_monads.distribution_semantics.ite
import computational_monads.distribution_semantics.prod

/-!
# Looking Up Cache Values with Fallback

This file defines a function `cache.get_or_else i t ou` that checks for a cached value of
`i, t`, and if not found runs `ou` to get a new result rather than returning `none`.
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

@[inline, reducible] def get_or_query (cache : query_cache spec) (i : spec.ι)
  (t : spec.domain i) := cache.get_or_else i t (query i t)

variables (cache cache' : query_cache spec)

section ite

variables (i : spec.ι) (t : spec.domain i) (ou : oracle_comp spec' (spec.range i))

lemma get_or_else_eq_ite : cache.get_or_else i t ou =
  if t ∈ᵢ cache then return ((cache.lookup i t).get_or_else default, cache)
    else ou >>= λ u, return (u, [i, t ↦ u; cache]) :=
begin
  split_ifs with h,
  { rw [mem_iff_exists_lookup_eq_some] at h,
    obtain ⟨u, hu⟩ := h,
    simp [get_or_else, hu] },
  { simp [get_or_else, lookup_eq_none_of_not_mem _ h] }
end

lemma support_get_or_else : (cache.get_or_else i t ou).support =
  if t ∈ᵢ cache then {((cache.lookup i t).get_or_else default, cache)}
    else (λ u, (u, [i, t ↦ u; cache])) '' ou.support :=
by simp [get_or_else_eq_ite]

lemma mem_support_get_or_else_iff (x : spec.range i × query_cache spec) :
  x ∈ (cache.get_or_else i t ou).support ↔
    if t ∈ᵢ cache then cache.lookup i t = some x.1 ∧ x.2 = cache
      else x.1 ∈ ou.support ∧ [i, t ↦ x.1; cache] = x.2 :=
begin
  split_ifs with h,
  { obtain ⟨u, hu⟩ := exists_lookup_eq_some_of_mem _ h,
    simp [get_or_else_eq_ite, h, prod.eq_iff_fst_eq_snd_eq, hu, eq_comm] },
  { simp [get_or_else_eq_ite, h],
    refine ⟨λ h', _, λ h', _⟩,
    { obtain ⟨u, hu⟩ := h',
      rw [prod.eq_iff_fst_eq_snd_eq] at hu,
      exact ⟨hu.2.1 ▸ hu.1, hu.2.1 ▸ hu.2.2⟩ },
    { exact ⟨x.1, h'.1, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, h'.2⟩⟩ } },
end

lemma eval_dist_get_or_else : ⁅cache.get_or_else i t ou⁆ =
  if t ∈ᵢ cache then pmf.pure ((cache.lookup i t).get_or_else default, cache)
    else ⁅ou⁆.map (λ u, (u, [i, t ↦ u; cache])) :=
by simp [get_or_else_eq_ite]

lemma prob_output_get_or_else (x) : ⁅= x | cache.get_or_else i t ou⁆ =
  if t ∈ᵢ cache then ⁅= x | return' !spec'! ((cache.lookup i t).get_or_else default, cache)⁆
    else ⁅= x | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆ :=
by simp [get_or_else_eq_ite]

lemma prob_event_get_or_else (e) : ⁅e | cache.get_or_else i t ou⁆ =
  if t ∈ᵢ cache then ⁅e | return' !spec! ((cache.lookup i t).get_or_else default, cache)⁆
    else ⁅e | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆ :=
by simp [get_or_else_eq_ite]

@[simp_dist_equiv] lemma get_or_else_dist_equiv : cache.get_or_else i t ou ≃ₚ
  if t ∈ᵢ cache then return ((cache.lookup i t).get_or_else default, cache)
    else ou >>= λ u, return (u, [i, t ↦ u; cache]) :=
by rw [get_or_else_eq_ite]

end ite

section mem

variables {i : spec.ι} {t : spec.domain i} (ou : oracle_comp spec' (spec.range i))

@[simp] lemma get_or_else_of_mem (h : t ∈ᵢ cache) :
  cache.get_or_else i t ou = return ((cache.lookup i t).get_or_else default, cache) :=
by simp only [get_or_else_eq_ite, h, if_true]

lemma support_get_or_else_of_mem (h : t ∈ᵢ cache) :
  (cache.get_or_else i t ou).support = {((cache.lookup i t).get_or_else default, cache)} :=
by simp [h]

lemma mem_support_get_or_else_iff_of_mem (h : t ∈ᵢ cache)
  (x : spec.range i × query_cache spec) : x ∈ (cache.get_or_else i t ou).support ↔
    cache.lookup i t = some x.1 ∧ x.2 = cache :=
by simp only [h, mem_support_get_or_else_iff, if_true]

lemma eval_dist_get_or_else_of_mem (h : t ∈ᵢ cache) :
  ⁅cache.get_or_else i t ou⁆ = pmf.pure ((cache.lookup i t).get_or_else default, cache) :=
by simp [h]

lemma prob_output_get_or_else_of_mem (h : t ∈ᵢ cache) (x) :
  ⁅= x | cache.get_or_else i t ou⁆ =
    ⁅= x | return' !spec'! ((cache.lookup i t).get_or_else default, cache)⁆ :=
by simp [h]

lemma prob_event_get_or_else_of_mem (h : t ∈ᵢ cache) (e) :
  ⁅e | cache.get_or_else i t ou⁆ =
    ⁅e | return' !spec! ((cache.lookup i t).get_or_else default, cache)⁆ :=
by simp [h]

lemma get_or_else_dist_equiv_of_mem (h : t ∈ᵢ cache) :
  cache.get_or_else i t ou ≃ₚ return' !spec! ((cache.lookup i t).get_or_else default, cache) :=
by simp [h]

end mem

section not_mem

variables {i : spec.ι} {t : spec.domain i} (ou : oracle_comp spec' (spec.range i))

@[simp] lemma get_or_else_of_not_mem (h : t ∉ᵢ cache) :
  cache.get_or_else i t ou = ou >>= λ u, return (u, [i, t ↦ u; cache]) :=
by simp [get_or_else, h]

lemma support_get_or_else_of_not_mem (h : t ∉ᵢ cache) :
  (cache.get_or_else i t ou).support = (λ u, (u, [i, t ↦ u; cache])) '' ou.support :=
by simp [h]

lemma mem_support_get_or_else_iff_of_not_mem (h : t ∉ᵢ cache)
  (x : spec.range i × query_cache spec) : x ∈ (cache.get_or_else i t ou).support ↔
    x.1 ∈ ou.support ∧ [i, t ↦ x.1; cache] = x.2 :=
by simp only [mem_support_get_or_else_iff, h, if_false]

lemma eval_dist_get_or_else_of_not_mem (h : t ∉ᵢ cache) :
  ⁅cache.get_or_else i t ou⁆ = ⁅ou⁆.map (λ u, (u, [i, t ↦ u; cache])) :=
by simp [h]

lemma prob_output_get_or_else_of_not_mem (h : t ∉ᵢ cache) (x) :
  ⁅= x | cache.get_or_else i t ou⁆ = ⁅= x | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆ :=
by simp [h]

lemma prob_event_get_or_else_of_not_mem (h : t ∉ᵢ cache) (e) :
  ⁅e | cache.get_or_else i t ou⁆ = ⁅e | ou >>= λ u, return (u, [i, t ↦ u; cache])⁆ :=
by simp [h]

lemma get_or_else_dist_equiv_of_not_mem (h : t ∉ᵢ cache) :
  cache.get_or_else i t ou ≃ₚ ou >>= λ u, return (u, [i, t ↦ u; cache]) :=
by rw [get_or_else_of_not_mem _ _ h]

end not_mem

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

@[simp] lemma get_or_else_empty : get_or_else ∅ i t ou = do {u ← ou, return (u, [i, t ↦ u])} :=
by simp [not_mem_empty i t, singleton.def]

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
    by_cases ht : t ∈ᵢ cache,
    { simp [ht] at h,
      simp [h, ht],
      split_ifs with htt; simp [htt] },
    { rw [mem_support_get_or_else_iff_of_not_mem _ _ ht] at h,
      simp [← h.2] } },
  { by_cases ht : t ∈ᵢ cache,
    { simp [ht] at h,
      simp [h, ht, hi] },
    { rw [mem_support_get_or_else_iff_of_not_mem _ _ ht] at h,
      simp [← h.2, hi] } }
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

lemma mem_of_mem_support_get_or_else
  (h : x ∈ (cache.get_or_else i t ou).support) : t ∈ᵢ x.2 :=
mem_of_lookup_eq_some _ (lookup_snd_eq_of_mem_support_get_or_else_same_input _ _ h)

end lookup

section order

variables {i : spec.ι} {t : spec.domain i} {ou : oracle_comp spec' (spec.range i)}
  (x : spec.range i × query_cache spec)

lemma le_of_mem_support_get_or_else (h : x ∈ (cache.get_or_else i t ou).support) : cache ≤ x.2 :=
begin
  by_cases ht : t ∈ᵢ cache,
  { rw [mem_support_get_or_else_iff_of_mem _ _ ht] at h,
    refine h.2 ▸ le_rfl },
  { rw [mem_support_get_or_else_iff_of_not_mem _ _ ht] at h,
    refine h.2 ▸ le_cache_query_self _ _ _ _ },
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
  by_cases h' : t ∈ᵢ cache,
  {

    have : t ∈ᵢ cache := sorry,
    simp [h', this, h],
    sorry,
  },
  {
    have : t ∉ᵢ cache' := sorry,
    simp [h, h', this],
  }
end

end fst_map

section bind_fst_map

variables

variables (i : spec.ι) (t : spec.domain i) (ou : oracle_comp spec' (spec.range i))
  (i' : spec.ι) (t' : spec.domain i') (ou' : oracle_comp spec' (spec.range i'))

theorem get_or_else_bind_fst_map_get_or_else_dist_equiv'
  (f : spec.range i × query_cache spec → query_cache spec)
  (hf : ∀ (x : spec.range i × query_cache spec), cache ≤ x.2 → cache ≤ f x ∧ f x ≤ x.2) :
  do {x ← cache.get_or_else i t ou, prod.fst <$> (f x).get_or_else i' t' ou'} ≃ₚ
    if h : i = i' then (if h.rec t = t'
      then (congr_arg spec.range h).rec (prod.fst <$> cache.get_or_else i t ou)
      else prod.fst <$> cache.get_or_else i' t' ou')
      else prod.fst <$> cache.get_or_else i' t' ou' :=
begin
  sorry,
end

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
      have := lookup_snd_eq_of_mem_support_get_or_else_diff_input _ _ _ ht hx,
      apply fst_map_get_or_else_dist_equiv_fst_map_get_or_else,
      exact this
    }
  },
  {
    simp [hi],
    refine bind_dist_equiv_right _ _ (default, cache) (λ x hx, _),
    have := lookup_snd_eq_of_mem_support_get_or_else_diff_index _ _ _ t' hi hx,
    apply fst_map_get_or_else_dist_equiv_fst_map_get_or_else,
    exact this
  }
end


@[simp_dist_equiv]
lemma get_or_else_bind_get_or_else_dist_equiv_same_input (t' : spec.domain i) :
  do {x ← cache.get_or_else i t ou, x.2.get_or_else i t' ou} ≃ₚ
    cache.get_or_else i t' ou :=
begin
  sorry
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

section bind_comm


end bind_comm

end query_cache