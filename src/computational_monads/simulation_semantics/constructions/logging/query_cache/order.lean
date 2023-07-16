/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.query_cache.basic
import computational_monads.distribution_semantics.option

/-!
# Ordering on Query Caches

This file defines a semilatice structure on `query_cache`, where `cache ≤ cache'` means
that any cached value in `cache` has the same value in `cache'`,
allowing any fresh value in `cache` to have any value (fresh or not) in `cache'`.

We also define and `inf` operation and a `⊥` element (the empty cache).
-/

namespace query_cache

open oracle_spec oracle_comp

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
    { cache_fn := λ i t, if (cache.is_cached i t ∧ cache.lookup i t = cache'.lookup i t)
        then cache.lookup i t else none,
      cached_inputs := sorry,
      mem_cached_inputs := sorry },
  inf_le_left := λ cache cache' i t u hu,
    begin
      by_cases h : cache.is_cached i t ∧ cache.lookup i t = cache'.lookup i t,
      { exact (if_pos h).symm.trans hu },
      { exact (option.some_ne_none u ((if_neg h).symm.trans hu).symm).elim }
    end,
  inf_le_right := λ cache cache' i t u hu,
    begin
      by_cases h : cache.is_cached i t ∧ cache.lookup i t = cache'.lookup i t,
      { exact h.2 ▸ (if_pos h).symm.trans hu },
      { exact (option.some_ne_none u ((if_neg h).symm.trans hu).symm).elim }
    end,
  le_inf := λ cache₁ cache₂ cache₃ h2 h3 i t u hu,
    begin
      by_cases h : cache₂.is_cached i t ∧ cache₂.lookup i t = cache₃.lookup i t,
      { exact (if_pos h).trans (h2 i t u hu) },
      { refine (not_and_distrib.1 h).rec (λ h, _) (λ h, _),
        { exact (h (is_cached_of_lookup_eq_some _ (h2 i t u hu))).elim },
        { exact (h ((h2 i t u hu).trans (h3 i t u hu).symm)).elim } }
    end }

variables (cache cache' : query_cache spec) (i : spec.ι) (t : spec.domain i) (u : spec.range i)

lemma le.def : cache ≤ cache' ↔
  ∀ i t u, cache.lookup i t = some u → cache'.lookup i t = some u := iff.rfl

section is_cached

lemma is_cached_of_le_of_is_cached {cache cache' : query_cache spec} {i t}
  (h : cache ≤ cache') (h' : cache.is_cached i t) :
  cache'.is_cached i t :=
begin
  rw [le.def] at h,
  rw [is_cached_iff_exists_lookup_eq_some] at ⊢ h',
  obtain ⟨u, hu⟩ := h',
  exact ⟨u, h i t u hu⟩,
end

end is_cached

section is_fresh

lemma is_fresh_of_le_of_is_fresh {cache cache' : query_cache spec} {i t}
  (h : cache ≤ cache') (h' : cache'.is_fresh i t) :
  cache.is_fresh i t :=
begin
  rw [← not_is_cached_iff_is_fresh] at h' ⊢,
  exact λ h'', h' (is_cached_of_le_of_is_cached h h'')
end

end is_fresh

section lookup

lemma lookup_eq_some_of_le {cache cache' : query_cache spec} {i t u}
  (h : cache ≤ cache') (h' : cache.lookup i t = some u) :
  cache'.lookup i t = some u := h i t u h'

lemma lookup_eq_lookup_of_le_of_is_cached {cache cache' : query_cache spec} {i t}
  (h : cache ≤ cache') (h' : cache.is_cached i t) :
  cache'.lookup i t = cache.lookup i t :=
let ⟨u, hu⟩ := lookup_eq_some_of_is_cached _ h' in (lookup_eq_some_of_le h hu).trans hu.symm

end lookup

section inf

lemma lookup_inf (i : spec.ι) (t : spec.domain i) : (cache ⊓ cache').lookup i t =
  if (cache.is_cached i t ∧ cache.lookup i t = cache'.lookup i t)
    then cache.lookup i t else none := rfl

end inf

section bot

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

end bot

section cache_query

lemma cache_query_monotone : monotone (cache_query i t u) :=
λ cache cache' h i' t' u', by {simp only [lookup_cache_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

lemma cache_query_le_cache_query_iff_of_is_fresh {cache cache' : query_cache spec} {i t} (u)
  (h : cache.is_fresh i t) (h' : cache'.is_fresh i t) :
    [i, t ↦ u; cache] ≤ [i, t ↦ u; cache'] ↔ cache ≤ cache' :=
begin
  refine ⟨λ hu i' t' u' hu', _, λ hu, cache_query_monotone i t u hu⟩,
  by_cases hi : i = i',
  -- TODO: could we write some kind of induction tactic thing for proofs like this?
  { induction hi,
    by_cases ht : t = t',
    { exact ((lookup_ne_some_of_is_fresh cache h u') (ht.symm ▸ hu')).elim },
    { specialize hu i t' u',
      simp only [lookup_cache_query_diff_input _ _ _ _ _ ht] at hu,
      exact hu hu' } },
  { specialize hu i' t' u',
    simp only [lookup_cache_query_diff_index _ _ _ _ _ _ hi] at hu,
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
    { exact h i t' u' ((lookup_cache_query_diff_input _ _ _ _ _ ht).symm.trans hu') } },
  { exact h i' t' u' ((lookup_cache_query_diff_index _ _ _ _ _ _ hi).symm.trans hu') }
end

@[simp] lemma le_cache_query_self : cache ≤ [i, t ↦ u; cache] := sorry

@[simp] lemma lt_cache_query_self_iff : cache < [i, t ↦ u; cache] ↔ cache.is_fresh i t := sorry

end cache_query

section drop_query

lemma drop_query_monotone : monotone (drop_query i t) :=
λ cache cache' h i' t' u', by {simp only [lookup_drop_query],
  split_ifs, exact id, exact h i' t' u', exact h i' t' u'}

@[simp] lemma drop_query_le_self : cache.drop_query i t ≤ cache := sorry

@[simp] lemma drop_query_lt_self_iff : cache.drop_query i t < cache ↔ cache.is_cached i t := sorry

@[simp] lemma drop_query_eq_init_iff_le_singleton : drop_query i t cache = ∅ ↔
  ∃ u, cache ≤ [i, t ↦ u] :=
sorry
-- begin
--   refine ⟨λ h, _, λ h, _⟩,
--   { by_cases h' : cache.is_fresh i t,
--     { rw [drop_query_of_is_fresh _ _ _ h'] at h,
--       exact ⟨default, h.symm ▸ init_le'⟩ },
--     { rw [← is_cached_iff_not_is_fresh, is_cached_iff_exists_lookup_eq_some] at h',
--       obtain ⟨u, hu⟩ := h',
--       refine ⟨u, λ i' t' u' hu', _⟩,
--       have := ((eq_init_iff _).1 h) i' t',
--       rw [is_fresh_drop_query_iff, ← lookup_eq_none_iff_is_fresh] at this,
--       refine this.rec_on (λ h', (option.some_ne_none u' (hu'.symm.trans h')).elim) _,
--       rintro ⟨rfl, rfl⟩,
--       exact (option.some_inj.1 (hu'.symm.trans hu)) ▸ (lookup_singleton_same_input _ _ _) } },
--   { obtain ⟨u, hu⟩ := h,
--     simp_rw [eq_init_iff, is_fresh_drop_query_iff, or_iff_not_imp_left,
--       ← is_cached_iff_not_is_fresh, is_cached_iff_exists_lookup_eq_some],
--     rintro i' t' ⟨u', hu'⟩,
--     obtain ⟨hi', ht', hu'⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 (hu i' t' u' hu'),
--     refine ⟨hi', ht'⟩ }
-- end


end drop_query

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

section singleton

lemma eq_singleton_iff : cache = [i, t ↦ u] ↔ cache ≤ [i, t ↦ u] ∧ cache ≠ ∅ :=
begin
  sorry,
  -- refine ⟨λ h, h.symm ▸ by simp, λ h, le_antisymm h.1 (λ i' t' u' h', _)⟩,
  -- obtain ⟨i'', t'', u'', h''⟩ := (ne_init_iff_exists_eq_some _).1 h.2,
  -- obtain ⟨hi, ht, hu⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 (h.1 i'' t'' u'' h''),
  -- obtain ⟨hi', ht', hu'⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 h',
  -- induction hi, induction hi',
  -- rwa [← ht', ← hu', ht, hu],
end


@[simp] lemma le_singleton_iff : cache ≤ [i, t ↦ u] ↔ cache = ∅ ∨ cache = [i, t ↦ u] :=
begin
  rw [eq_singleton_iff, and_comm],
  refine ⟨λ h, _, λ h, h.rec_on (λ h', le_of_eq_of_le h' (init_le _)) (λ h, h.2)⟩,
  by_cases h' : cache = ∅,
  { exact or.inl h' },
  { exact or.inr ⟨h', h⟩ }
end



lemma le_singleton_iff_forall : cache ≤ [i, t ↦ u] ↔ ∀ i' t', cache.is_cached i' t' →
  ∃ (h : i = i'), h.rec t = t' ∧ cache.lookup i' t' = some (h.rec u)  :=
⟨λ h i' t' ht', let ⟨u', hu'⟩ := (cache.is_cached_iff_exists_lookup_eq_some _ _).1 ht' in
  let ⟨hi, ht, hu⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 (h i' t' u' hu') in
    ⟨hi, ht, hu.symm ▸ hu'⟩, λ h i' t' u' hu', (lookup_singleton_eq_some_iff _ _ _ _ _ _).2
      (let ⟨hi, ht, hu⟩ := h i' t' (is_cached_of_lookup_eq_some _ hu') in
        ⟨hi, ht, option.some_inj.1 (hu.symm.trans hu')⟩)⟩


@[simp] lemma lt_singleton_iff : cache < [i, t ↦ u] ↔ cache = ∅ :=
begin
  rw [lt_iff_le_and_ne, le_singleton_iff, or_and_distrib_right,
    and_not_self, or_false, and_iff_left_iff_imp],
  exact λ h, h.symm ▸ (ne.symm (singleton_ne_init i t u))
end

@[simp] lemma singleton_le_iff : [i, t ↦ u] ≤ cache ↔ cache.lookup i t = some u :=
begin
  refine ⟨λ h, h i t u (lookup_singleton_same_input i t u), λ h i' t' u' h', _⟩,
  obtain ⟨rfl, rfl, rfl⟩ := (lookup_singleton_eq_some_iff _ _ _ _ _ _).1 h',
  exact h,
end

end singleton

end query_cache