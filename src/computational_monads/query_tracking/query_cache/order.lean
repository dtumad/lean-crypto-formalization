/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_cache.basic

/-!
# Ordering on Query Caches

This file defines a semilatice structure on `query_cache`, where `cache ≤ cache'` means
that any cached value in `cache` has the same value in `cache'`,
allowing any fresh value in `cache` to have any value (fresh or not) in `cache'`.

We also define and `inf` operation and a `⊥` element (the empty cache).
-/

namespace query_cache

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- We say `cache ≤ cache'` for two query caches if every cached value in `cache` has the same
value cached in `cache'`. For fresh values in `cache` the corresponding value can be anything.
We also have an `inf` operation that only returns values cached in both original caches. -/
instance : semilattice_inf (query_cache spec) :=
{ le := λ cache cache', ∀ i t u, cache.lookup i t = some u → cache'.lookup i t = some u,
  le_refl := λ cache i t u h, h,
  le_trans := λ cache cache' cache'' h h' i t u h'', h' i t u (h i t u h''),
  le_antisymm := λ cache cache' h' h, query_cache.extₗ (λ i t,
    begin
      by_cases hi : cache.lookup i t = none,
      { by_cases hi' : cache'.lookup i t = none,
        { rw [hi, hi'] },
        { obtain ⟨u, hu⟩ := option.ne_none_iff_exists'.1 hi',
          refine (option.some_ne_none u ((h i t u hu).symm.trans hi)).elim } },
      { exact let ⟨u, hu⟩ := option.ne_none_iff_exists'.1 hi in (hu.trans (h' i t u hu).symm) }
    end),
  inf := λ cache cache',
    { cache_fn := λ i t, if (t ∈ᵢ cache ∧ cache.lookup i t = cache'.lookup i t)
        then cache.lookup i t else none,
      cached_inputs := sorry,
      mem_cached_inputs := sorry },
  inf_le_left := λ cache cache' i t u hu,
    begin
      by_cases h : t ∈ᵢ cache ∧ cache.lookup i t = cache'.lookup i t,
      { exact (if_pos h).symm.trans hu },
      { exact (option.some_ne_none u ((if_neg h).symm.trans hu).symm).elim }
    end,
  inf_le_right := λ cache cache' i t u hu,
    begin
      by_cases h : t ∈ᵢ cache ∧ cache.lookup i t = cache'.lookup i t,
      { exact h.2 ▸ (if_pos h).symm.trans hu },
      { exact (option.some_ne_none u ((if_neg h).symm.trans hu).symm).elim }
    end,
  le_inf := λ cache₁ cache₂ cache₃ h2 h3 i t u hu,
    begin
      by_cases h : t ∈ᵢ cache₂  ∧ cache₂.lookup i t = cache₃.lookup i t,
      { exact (if_pos h).trans (h2 i t u hu) },
      { refine (not_and_distrib.1 h).rec (λ h, _) (λ h, _),
        { exact (h (mem_of_lookup_eq_some _ (h2 i t u hu))).elim },
        { exact (h ((h2 i t u hu).trans (h3 i t u hu).symm)).elim } }
    end }

variables (cache cache' : query_cache spec) (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma le.def : cache ≤ cache' ↔
  ∀ i t u, cache.lookup i t = some u → cache'.lookup i t = some u := iff.rfl

lemma mem_of_le_of_mem {cache cache' : query_cache spec} {i : spec.ι} {t : spec.domain i}
  (h : cache ≤ cache') (h' : t ∈ᵢ cache) : t ∈ᵢ cache' :=
begin
  rw [mem_iff_exists_lookup_eq_some] at ⊢ h',
  exact let ⟨u, hu⟩ := h' in ⟨u, h i t u hu⟩,
end

lemma not_mem_of_le_of_not_mem {cache cache' : query_cache spec} {i : spec.ι} {t : spec.domain i}
  (h : cache ≤ cache') (h' : t ∉ᵢ cache') : t ∉ᵢ cache :=
λ h'', h' (mem_of_le_of_mem h h'')

lemma cached_inputs_subset_cached_inputs_of_le {cache cache' : query_cache spec}
  (h : cache ≤ cache') : cache.cached_inputs ⊆ cache'.cached_inputs :=
begin
  intros x hx,
  rw [← mem_iff_mem_cached_inputs'] at hx ⊢,
  refine mem_of_le_of_mem h hx,
end

section lookup

lemma lookup_eq_some_of_le {cache cache' : query_cache spec} {i t u}
  (h : cache ≤ cache') (h' : cache.lookup i t = some u) :
  cache'.lookup i t = some u := h i t u h'

lemma lookup_eq_lookup_of_le_of_mem {cache cache' : query_cache spec} {i t}
  (h : cache ≤ cache') (h' : t ∈ᵢ cache) : cache'.lookup i t = cache.lookup i t :=
let ⟨u, hu⟩ := exists_lookup_eq_some_of_mem _ h' in (lookup_eq_some_of_le h hu).trans hu.symm

end lookup

section inf

lemma lookup_inf (i : spec.ι) (t : spec.domain i) : (cache ⊓ cache').lookup i t =
  if (t ∈ᵢ cache ∧ cache.lookup i t = cache'.lookup i t) then cache.lookup i t else none := rfl

end inf

section bot

/-- The "smallest" element in the `query_cache` ordering is the empty cache. -/
instance : order_bot (query_cache spec) :=
{ bot := ∅,
  bot_le := λ cache i t u h, (lookup_empty_ne_some i t u h).elim }

lemma bot_eq_empty (spec : oracle_spec) : (⊥ : query_cache spec) = ∅ := rfl

@[simp] lemma empty_le : ∅ ≤ cache := bot_le

lemma empty_le' {cache : query_cache spec} : ∅ ≤ cache := bot_le

@[simp] lemma empty_lt_iff : ∅ < cache ↔ cache ≠ ∅ := bot_lt_iff_ne_bot

@[simp] lemma le_empty_iff : cache ≤ ∅ ↔ cache = ∅ := le_bot_iff

@[simp] lemma not_lt_empty : ¬ cache < ∅ := not_lt_bot

@[simp] lemma inf_empty : cache ⊓ ∅ = ∅ := inf_bot_eq

@[simp] lemma empty_inf : ∅ ⊓ cache = ∅ := bot_inf_eq

end bot

section cache_query

lemma cache_query_monotone : monotone (cache_query i t u) :=
λ cache cache' h i' t' u', by {simp only [lookup_cache_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

lemma cache_query_le_cache_query_iff_of_not_mem {cache cache' : query_cache spec} {i t} (u)
  (h : t ∉ᵢ cache) (h' : t ∉ᵢ cache') : [i, t ↦ u; cache] ≤ [i, t ↦ u; cache'] ↔ cache ≤ cache' :=
begin
  refine ⟨λ hu i' t' u' hu', _, λ hu, cache_query_monotone i t u hu⟩,
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t',
    { exact ((lookup_ne_some_of_not_mem cache h u') (ht.symm ▸ hu')).elim },
    { specialize hu i t' u',
      simp only [lookup_cache_query_diff_input _ _ ht] at hu,
      exact hu hu' } },
  { specialize hu i' t' u',
    simp only [lookup_cache_query_diff_index _ hi] at hu,
    exact hu hu' }
end

lemma cache_query_le_iff_of_le {cache cache' : query_cache spec}
  (h : cache ≤ cache') (i t u) : [i, t ↦ u; cache] ≤ cache' ↔ cache'.lookup i t = some u :=
begin
  refine ⟨λ h', h' i t u (lookup_cache_query_same_input _ i t u), λ h' i' t' u' hu', _⟩,
  by_cases hi : i = i',
  { induction hi,
    by_cases ht : t = t',
    { induction ht,
      refine trans h' ((lookup_cache_query_same_input _ _ _ _).symm.trans hu') },
    { exact h i t' u' ((lookup_cache_query_diff_input _ _ ht _).symm.trans hu') } },
  { exact h i' t' u' ((lookup_cache_query_diff_index _ hi _ _ _).symm.trans hu') }
end

@[simp] lemma le_cache_query_self : cache ≤ [i, t ↦ u; cache] := sorry

@[simp] lemma lt_cache_query_self_iff : cache < [i, t ↦ u; cache] ↔ t ∉ᵢ cache := sorry

end cache_query

section drop_query

lemma drop_query_monotone : monotone (drop_query i t) :=
λ cache cache' h i' t' u', by {simp only [lookup_drop_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

@[simp] lemma drop_query_le_self : cache.drop_query i t ≤ cache := sorry

@[simp] lemma drop_query_lt_self_iff : cache.drop_query i t < cache ↔ t ∈ᵢ cache := sorry

@[simp] lemma drop_query_eq_empty_iff_le_singleton :
  drop_query i t cache = ∅ ↔ ∃ u, cache ≤ [i, t ↦ u] :=
sorry

end drop_query

@[simp] lemma le_cache_query_iff : cache ≤ [i, t ↦ u; cache'] ↔
  (t ∉ᵢ cache ∨ cache.lookup i t = some u) ∧ (cache.drop_query i t ≤ cache'.drop_query i t) :=
begin
  sorry,
end

@[simp] lemma cache_query_le_iff : [i, t ↦ u; cache] ≤ cache' ↔
  cache'.lookup i t = some u ∧ cache.drop_query i t ≤ cache' :=
begin
  sorry
end

section singleton

lemma eq_singleton_iff_le_and_not_empty : cache = [i, t ↦ u] ↔ cache ≤ [i, t ↦ u] ∧ cache ≠ ∅ :=
begin
  sorry,
  -- refine ⟨λ h, h.symm ▸ by simp, λ h, le_antisymm h.1 (λ i' t' u' h', _)⟩,
  -- obtain ⟨i'', t'', u'', h''⟩ := (ne_empty_iff_exists_eq_some _).1 h.2,
  -- obtain ⟨hi, ht, hu⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 (h.1 i'' t'' u'' h''),
  -- obtain ⟨hi', ht', hu'⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 h',
  -- induction hi, induction hi',
  -- rwa [← ht', ← hu', ht, hu],
end

@[simp] lemma le_singleton_iff : cache ≤ [i, t ↦ u] ↔ cache = ∅ ∨ cache = [i, t ↦ u] :=
begin
  rw [eq_singleton_iff_le_and_not_empty, and_comm],
  refine ⟨λ h, _, λ h, h.rec_on (λ h', le_of_eq_of_le h' (empty_le _)) (λ h, h.2)⟩,
  by_cases h' : cache = ∅,
  { exact or.inl h' },
  { exact or.inr ⟨h', h⟩ }
end


lemma le_singleton_iff_forall : cache ≤ [i, t ↦ u] ↔ ∀ i' t', t' ∈ᵢ cache →
  ∃ (h : i = i'), h.rec t = t' ∧ cache.lookup i' t' = some (h.rec u)  :=
⟨λ h i' t' ht', let ⟨u', hu'⟩ := (cache.mem_iff_exists_lookup_eq_some _ _).1 ht' in
  let ⟨hi, ht, hu⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 (h i' t' u' hu') in
    ⟨hi, ht, hu.symm ▸ hu'⟩, λ h i' t' u' hu', (lookup_singleton_eq_some_iff _ _ _ _ _ _).2
      (let ⟨hi, ht, hu⟩ := h i' t' (mem_of_lookup_eq_some _ hu') in
        ⟨hi, ht, option.some_inj.1 (hu.symm.trans hu')⟩)⟩


@[simp] lemma lt_singleton_iff : cache < [i, t ↦ u] ↔ cache = ∅ :=
begin
  rw [lt_iff_le_and_ne, le_singleton_iff, or_and_distrib_right,
    and_not_self, or_false, and_iff_left_iff_imp],
  exact λ h, h.symm ▸ (ne.symm (singleton_ne_empty i t u))
end

@[simp] lemma singleton_le_iff : [i, t ↦ u] ≤ cache ↔ cache.lookup i t = some u :=
begin
  refine ⟨λ h, h i t u (lookup_singleton_same_input i t u), λ h i' t' u' h', _⟩,
  obtain ⟨rfl, rfl, rfl⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 h',
  exact h,
end

end singleton

end query_cache