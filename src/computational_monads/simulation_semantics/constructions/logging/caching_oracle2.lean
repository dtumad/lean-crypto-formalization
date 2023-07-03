/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.query_cache.get_or_else
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.distribution_semantics.prod
import computational_monads.distribution_semantics.query
import computational_monads.constructions.product

/-!
# Caching Simulation Oracle

This file defines a `sim_oracle` that implements caching functionality.
`cachingₛₒ` represents a simulator that caches fresh queries and returns the same value
for any future queries, using a `query_cache` as an internal state for tracking this.

This is used by being composed with other oracles, such as in `random_oracle`.
-/

open oracle_comp oracle_spec query_cache
open prod (fst) (snd)
open_locale ennreal big_operators

variables {α β γ δ : Type} {spec spec' : oracle_spec}

/-- Oracle for tracking previous queries, and returning the same value for matching inputs.
The `query_cache.get_or_else` function allows us to run a fallback for non-cached values. -/
def cachingₛₒ {spec : oracle_spec} : sim_oracle spec spec (query_cache spec) :=
{ default_state := ∅,
  o := λ i ⟨t, cache⟩, cache.get_or_else i t (query i t) }

namespace cachingₛₒ

@[simp] lemma apply_eq (i : spec.ι) (x : spec.domain i × query_cache spec) :
  cachingₛₒ i x = x.2.get_or_else i x.1 (query i x.1) := by cases x; refl

-- lemma better ()


@[simp_dist_equiv] lemma fst_map_apply_bind_apply_dist_equiv''
  (i : spec.ι) (t : spec.domain i) (i' : spec.ι) (t' : spec.domain i') (cache : query_cache spec)
  (f : spec.range i' × query_cache spec → query_cache spec) :
  do {x ← cachingₛₒ i' (t', cache), fst <$> cachingₛₒ i (t, f x)} ≃ₚ
    fst <$> cachingₛₒ i (t, cache) :=
begin
  simp,
  have := get_or_else_bind_fst_map_get_or_else_dist_equiv' cache i' t' (query i' t')
    i t (query i t) f sorry,
  refine this.trans _,
  -- refine trans (by apply get_or_else_bind_fst_map_get_or_else_dist_equiv') _,
  split_ifs with hi ht,
  induction hi,
  simp [← ht],
  pairwise_dist_equiv,
  pairwise_dist_equiv,
end

@[simp_dist_equiv] lemma fst_map_apply_bind_apply_dist_equiv'
  (i : spec.ι) (t : spec.domain i) (i' : spec.ι) (t' : spec.domain i') (cache : query_cache spec) :
  do {x ← cachingₛₒ i' (t', cache), fst <$> cachingₛₒ i (t, x.2)} ≃ₚ
    fst <$> cachingₛₒ i (t, cache) :=
begin
  refine trans (by apply get_or_else_bind_fst_map_get_or_else_dist_equiv) _,
  split_ifs with hi ht,
  induction hi,
  simp [← ht],
  pairwise_dist_equiv,
  pairwise_dist_equiv,
end

lemma shorter (oa : oracle_comp spec α) --(s : query_cache spec)
  (f : α × query_cache spec → query_cache spec)
  (hf : ∀ z, ∅ ≤ f z ∧ f z ≤ z.2)
  (z : α × query_cache spec)
  (hz : z ∈ (simulate cachingₛₒ oa ∅).support) :
  ⁅= z | simulate cachingₛₒ oa ∅⁆ ≤
    ⁅= z | simulate cachingₛₒ oa (f z)⁆ :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i' t' generalizing f,
  {
    rw [mem_support_simulate_return_iff] at hz,
    have : f z = ∅ := le_antisymm (hz.2 ▸ (hf z).2) (hf z).1,
    exact le_of_eq (this ▸ rfl)
  },
  {
    simp only [] at hoa hob,
    simp [prob_output_simulate'_bind_eq_tsum_tsum],

    refine ennreal.tsum_le_tsum (λ x, ennreal.tsum_le_tsum (λ s', _)),
    specialize hoa (x, s'),
    sorry,
  },
  {
    sorry,
  }
end

-- #check antitone

-- #check exists.rec

lemma maybe (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (s : query_cache spec) (z : β) (cache : query_cache spec)
  (hz : (z, cache) ∈ (simulate cachingₛₒ (oa >>= ob) s).support) :
  ∃! (y : α × query_cache spec), y ∈ (simulate cachingₛₒ oa s).support ∧
    (z, cache) ∈ (simulate cachingₛₒ (ob y.1) y.2).support :=
begin
  rw [mem_support_simulate_bind_iff] at hz,
  obtain ⟨x, s', hx, hs'⟩ := hz,
  refine ⟨(x, s'), ⟨hx, hs'⟩, _⟩,
  rintro ⟨x', s''⟩ ⟨hx', hx''⟩,
  sorry,
end

-- def midpoint (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
--   (s : query_cache spec) (z : β × query_cache spec)
--   (hz : z ∈ (simulate cachingₛₒ (oa >>= ob) s).support) : α × query_cache spec :=
-- begin
--   induction oa using oracle_comp.induction_on
--     with α a α β oa ob hoa hob i t generalizing,
--   {

--   }

-- end

/-- Probability of getting to a final result given a partial cache for queries is given by
the product of probabilities that each additional query gets the expected result. -/
lemma finite_version (oa : oracle_comp spec α) (cache : query_cache spec)
  (z : α × query_cache spec) (h : cache ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa cache).support) :
  ⁅= z | simulate cachingₛₒ oa cache⁆ =
    ∏ i in (z.2.cached_inputs \ cache.cached_inputs), (fintype.card $ spec.range i.1)⁻¹ :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing,
  {
    simp only [support_simulate_return, set.mem_singleton_iff] at hz,
    simp only [hz, prob_output_simulate_return_eq_indicator, set.indicator_of_mem,
      set.mem_singleton, finset.sdiff_self, finset.prod_empty],
  },
  {
    rw [prob_output_simulate_bind_eq_tsum_tsum],
    sorry,
  },
  {
    simp [simulate_query, apply_eq] at hz ⊢,
    sorry,
  }
end

-- lemma maybe2 (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
--   (s : query_cache spec) (z : β × query_cache spec)
--   (hz : z ∈ (simulate cachingₛₒ (oa >>= ob) s).support) :
--   ∃! (y : α × query_cache spec),
--     ⁅= z | simulate cachingₛₒ (oa >>= ob) s⁆ =
--       ⁅= y | simulate cachingₛₒ oa s⁆ * ⁅= z | simulate cachingₛₒ (ob y.1) y.2⁆ :=
-- begin
--   rw [mem_support_simulate_bind_iff] at hz,
--   obtain ⟨x, s', hx, hs'⟩ := hz,
--   refine ⟨(x, s'), _⟩,
--   {
--     simp,
--   }
-- end

-- def substitute_cache (cache : query_cache spec) :
--   Π {α : Type}, oracle_comp spec α → oracle_comp spec α
-- | _ (pure' α a) := return a
-- | _ (bind' α β oa ob) := (substitute_cache oa) >>= (λ x, substitute_cache (ob x))
-- | _ (query i t) := if cache.is_cached i t then
--   return ((cache.lookup i t).get_or_else default) else query i t

-- -- def full_substitute_cache

-- /-- Extra choices to be made while running a computation to get from an
-- initial cache of `s` to a cache of `cache` (assuming it's possible to do so)-/
-- noncomputable def extra_choices (s cache : query_cache spec) :
--   Π {α : Type}, oracle_comp spec α → finset (Σ (i : spec.ι), spec.domain i)
-- | _ (pure' α a) := ∅
-- | _ (bind' α β oa ob) := (extra_choices oa) ∪
--   ((substitute_cache cache oa).fin_support.bUnion (λ x, extra_choices (ob x)))
-- | _ (query i t) := if s.is_fresh i t then {⟨i, t⟩} else ∅

-- lemma extra_choices_return (s cache : query_cache spec) (x : α) :
--   extra_choices s cache (return x) = ∅ := rfl

-- lemma extra_choices_bind (s cache : query_cache spec) (oa : oracle_comp spec α)
--   (ob : α → oracle_comp spec β) : extra_choices s cache (oa >>= ob) = (extra_choices s cache oa) ∪
--     ((substitute_cache cache oa).fin_support.bUnion (λ x, extra_choices s cache (ob x))):=
-- begin
--   rw [← bind'_eq_bind, extra_choices],
-- end

-- lemma extra_choices_query (s cache : query_cache spec) (i : spec.ι) (t : spec.domain i) :
--   extra_choices s cache (query i t) =
--     if s.is_fresh i t then {⟨i, t⟩} else ∅ := rfl

-- theorem hope (oa : oracle_comp spec α) (s cache : query_cache spec) (hs : s ≤ cache)
--   (x : α) (hx : (x, cache) ∈ (simulate cachingₛₒ oa s).support) :
--   ⁅= (x, cache) | simulate cachingₛₒ oa s⁆ =
--     ∏ i in extra_choices s cache oa, (fintype.card $ spec.range i.1)⁻¹ :=
-- begin
--   induction oa using oracle_comp.induction_on
--     with α a α β oa ob hoa hob i t generalizing s cache,
--   {
--     rw [extra_choices_return, finset.prod_empty, simulate_return,
--       prob_output_return_eq_one_iff],
--     rwa [simulate_return, mem_support_return_iff] at hx,
--   },
--   {
--     rw [extra_choices_bind, finset.prod_union sorry],
--     rw [prob_output_simulate_bind_eq_tsum_tsum],
--   },
--   {
--     rw [extra_choices_query],
--     split_ifs with h,
--     {
--       rw [finset.prod_singleton, simulate_query, apply_eq],
--       rw [simulate_query, apply_eq] at hx,
--       simp [h] at hx ⊢,
--       rw [← hx],
--       refine trans (prob_output_bind_return_eq_single' _ _ _ x rfl _) _,
--       refine λ _ _ h', (prod.eq_iff_fst_eq_snd_eq.1 h').1,
--       rw [prob_output_query_eq_inv],
--     },
--     {
--       rw [finset.prod_empty],
--       rw [not_is_fresh_iff_is_cached] at h,
--       simp [h, simulate_query, apply_eq] at ⊢ hx,
--       intros x' s' hx' hs',
--       refine ⟨hx'.trans hx.1.symm, hs'.trans hx.2.symm⟩,
--     }
--   }
-- end

-- -- theorem testing (s cache : query_cache spec) ()

-- -- lemma exists_list (oa : oracle_comp spec α) (s cache : query_cache spec)
-- --   (z : α) :
-- --   ∃ (qs : list spec.ι), ⁅= (z, cache) | simulate cachingₛₒ oa s⁆ =
-- --     (qs.map (λ i, )) :=
-- -- begin

-- -- end

-- lemma output_eq_of_state_eq (oa : oracle_comp spec α)
--   (s s' : query_cache spec) (hs : s ≤ s')
--   (x x' : α) (cache : query_cache spec)
--   (h : (x, cache) ∈ (simulate cachingₛₒ oa s).support)
--   (h' : (x', cache) ∈ (simulate cachingₛₒ oa s).support) :
--   x = x' :=
-- begin
--   induction oa using oracle_comp.induction_on
--     with α a α β oa ob hoa hob i t generalizing s cache,
--   {
--     simp at h h',
--     simp [h.1, h'.1]
--   },
--   {
--     rw [mem_support_simulate_bind_iff] at h h',
--     obtain ⟨a, s, hs, hxa⟩ := h,
--     obtain ⟨a', s', hs', hxa'⟩ := h',
--     specialize hoa a a',
--     specialize hob a x x',
--   }
-- end

-- -- lemma prob_output_mono_bot (oa : oracle_comp spec α) (s : query_cache spec)
-- --   (z : α × query_cache spec) (hz : s ≤ z.2) :
-- --   ⁅= z | simulate cachingₛₒ oa ∅⁆ ≤ ⁅= z | simulate cachingₛₒ oa s⁆ :=
-- -- begin
-- --   induction oa using oracle_comp.induction_on
-- --     with α a α β oa ob hoa hob i t generalizing s hz,

-- --   {
-- --     sorry,
-- --   },
-- --   {
-- --     -- simp only [] at hoa hob,
-- --     simp only [simulate_bind],
-- --     simp only [prob_output_bind_eq_tsum, ennreal.tsum_prod'],
-- --     refine ennreal.tsum_le_tsum (λ x, _),


-- --   }
-- -- end


-- lemma support_antitone (oa : oracle_comp spec α) (s s' : query_cache spec)
--   (hs : s ≤ s') : (simulate' cachingₛₒ oa s').support ⊆ (simulate' cachingₛₒ oa s).support :=
-- begin
--   induction oa using oracle_comp.induction_on
--     with α a α β oa ob hoa hob i t generalizing s s',
--   {
--     -- rw [simulate_return, simulate_return],
--     simp,
--   },
--   sorry,
--   sorry,
-- end

-- lemma prob_output_mono (oa : oracle_comp spec α) (s s' : query_cache spec)
--   (hs : s ≤ s') (z : α × query_cache spec) (hz : s' ≤ z.2) :
--   ⁅= z | simulate cachingₛₒ oa s⁆ ≤ ⁅= z | simulate cachingₛₒ oa s'⁆ :=
-- begin
--   -- by_cases h : z ∈ (simulate cachingₛₒ oa s').support,
--   -- {
--   --   have h' : z ∈ (simulate cachingₛₒ oa s).support := sorry,
--   -- }
--   cases z,
--   rw [hope, hope]; sorry
--   -- induction oa using oracle_comp.induction_on
--   --   with α a α β oa ob hoa hob i t generalizing s s',
--   -- {
--   --   rw [simulate_return, simulate_return],
--   --   by_cases h : z = (a, s'),
--   --   {
--   --     simp [h],
--   --   },
--   --   {
--   --     have : z ≠ (a, s) := sorry,
--   --     rw [(prob_output_return_eq_zero_iff _ _ _).2 h,
--   --       (prob_output_return_eq_zero_iff _ _ _).2 this],
--   --     refine le_rfl,
--   --   }
--   -- },
--   -- {
--   --   simp only [simulate_bind],
--   --   simp only [prob_output_bind_eq_tsum],
--   --   simp only [ennreal.tsum_prod'],
--   --   -- simp_rw [@ennreal.tsum_comm α],
--   --   refine ennreal.tsum_le_tsum (λ x, _),


--   --   sorry,



--   -- },
--   -- {
--   --   simp only [simulate_query, apply_eq],
--   --   by_cases ht : s.is_fresh i t,
--   --   {
--   --     by_cases ht' : s'.is_fresh i t,
--   --     {
--   --       simp [ht, ht'],
--   --     }
--   --   }
--   -- }
-- end



-- lemma fork_thing_harder (oa : oracle_comp spec α)  (s : query_cache spec)
--   (f : α × query_cache spec → query_cache spec)
--   (hf : ∀ z, s ≤ f z ∧ f z ≤ z.2) (z : α × query_cache spec) :
--   ⁅= (z, z) | do {z1 ← simulate cachingₛₒ oa s,
--       z2 ← simulate cachingₛₒ oa s, return (z1, z2)}⁆ ≤
--     ⁅= (z, z) | do {z1 ← simulate cachingₛₒ oa s,
--       z2 ← simulate cachingₛₒ oa (f z1), return (z1, z2)}⁆ :=
-- begin
--   induction oa using oracle_comp.induction_on
--     with α a α β oa ob hoa hob i t generalizing s f,
--   {
--     have : f (a, s) = s := sorry,
--     simp [simulate_return, this],
--   },
--   {
--     calc ⁅= (z, z) | do {z1 ← simulate cachingₛₒ (oa >>= ob) s,
--         z2 ← simulate cachingₛₒ (oa >>= ob) s, return (z1, z2)}⁆ =
--       ⁅= (z, z) | do {x1 ← simulate cachingₛₒ oa s,
--         z1 ← simulate cachingₛₒ (ob x1.1) x1.2,
--         x2 ← simulate cachingₛₒ oa s,
--         z2 ← simulate cachingₛₒ (ob x2.1) x2.2,
--         return (z1, z2)}⁆ : sorry

--       ... ≤ ⁅= (z, z) | do {x1 ← simulate cachingₛₒ oa s,
--         z1 ← simulate cachingₛₒ (ob x1.1) x1.2,
--         x2 ← simulate cachingₛₒ oa (f z1),
--         z2 ← simulate cachingₛₒ (ob x2.1) x2.2,
--         return (z1, z2)}⁆ : sorry
--       ... = ⁅= (z, z) | do {z1 ← simulate cachingₛₒ (oa >>= ob) s,
--         z2 ← simulate cachingₛₒ (oa >>= ob) (f z1), return (z1, z2)}⁆ : sorry

--   },
--   sorry,
-- end

-- lemma fork_thing (oa : oracle_comp spec α)  (s : query_cache spec)
--   (f : α × query_cache spec → query_cache spec)
--   (hf : ∀ z, s ≤ f z ∧ f z ≤ z.2) (x : α) :
--   ⁅= (x, x) | do {simulate' cachingₛₒ oa s ×ₘ simulate' cachingₛₒ oa s}⁆ ≤
--     ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s,
--       z' ← simulate' cachingₛₒ oa (f z), return (z.1, z')}⁆ :=
-- begin
--   rw [product.def],
--   -- refine le_trans (le_of_eq $ prob_output_product _ _ (x, x)) _,
--   induction oa using oracle_comp.induction_on
--     with α a α β oa ob hoa hob i t generalizing s f,
--   {
--     refine le_of_eq (dist_equiv.prob_output_eq (symm (trans
--       (simulate_bind_dist_equiv_simulate'_bind _ _ _ s s (λ _ _, _)) _)) _); pairwise_dist_equiv },
--   {
--     simp only [] at hoa hob,

--     -- sorry,

--     -- suffices : ∀ z ∈ (simulate cachingₛₒ (oa >>= ob) s).support,
--     --   ⁅= fst z | simulate' cachingₛₒ (oa >>= ob) s⁆ ≤
--     --     ⁅= fst z | simulate' cachingₛₒ (oa >>= ob) (f z)⁆,
--     -- {

--     -- }

--     calc ⁅= (x, x) | simulate' cachingₛₒ (oa >>= ob) s >>= λ z,
--         simulate' cachingₛₒ (oa >>= ob) s >>= λ z',
--         return (z, z')⁆ =
--       ⁅= (x, x) | (simulate cachingₛₒ oa s >>= λ x,
--         simulate' cachingₛₒ (ob x.1) x.2) >>= λ z,
--         (simulate cachingₛₒ oa s >>= λ x',
--         simulate' cachingₛₒ (ob x'.1) x'.2) >>= λ z',
--         return (z, z')⁆ : by pairwise_dist_equiv

--       ... = ⁅= (x, x) | simulate cachingₛₒ oa s >>= λ x,
--         simulate' cachingₛₒ (ob x.1) x.2 >>= λ z,
--         (simulate cachingₛₒ oa s >>= λ x',
--         simulate' cachingₛₒ (ob x'.1) x'.2) >>= λ z',
--         return (z, z')⁆ : by pairwise_dist_equiv

--       ... = ⁅= (x, x) | simulate cachingₛₒ oa s >>= λ x,
--         simulate' cachingₛₒ (ob x.1) x.2 >>= λ z,
--         simulate cachingₛₒ oa s >>= λ x',
--         simulate' cachingₛₒ (ob x'.1) x'.2 >>= λ z',
--         return (z, z')⁆ : by pairwise_dist_equiv

--       ... = ⁅= (x, x) | simulate cachingₛₒ oa s >>= λ x,
--         simulate cachingₛₒ (ob x.1) x.2 >>= λ z,
--         simulate cachingₛₒ oa s >>= λ x',
--         simulate' cachingₛₒ (ob x'.1) x'.2 >>= λ z',
--         return (z.1, z')⁆ : by pairwise_dist_equiv

--       ... ≤ ⁅= (x, x) | simulate cachingₛₒ oa s >>= λ x,
--         simulate cachingₛₒ (ob x.1) x.2 >>= λ z,
--         simulate cachingₛₒ oa (f z) >>= λ x',
--         simulate' cachingₛₒ (ob x'.1) x'.2 >>= λ z',
--         return (z.1, z')⁆ :
--           begin

--           end

--       ... = ⁅= (x, x) | (simulate cachingₛₒ oa s >>= λ x,
--         simulate cachingₛₒ (ob x.1) x.2) >>= λ z,
--         simulate cachingₛₒ oa (f z) >>= λ x',
--         simulate' cachingₛₒ (ob x'.1) x'.2 >>= λ z',
--         return (z.1, z')⁆ : by pairwise_dist_equiv

--       ... = ⁅= (x, x) | simulate cachingₛₒ (oa >>= ob) s >>= λ z,
--         simulate' cachingₛₒ (oa >>= ob) (f z) >>= λ z',
--         return (z.1, z')⁆ : begin
--           pairwise_dist_equiv,
--           refine trans (by pairwise_dist_equiv) (bind_dist_equiv_bind_of_dist_equiv_left _ _ _
--             (simulate'_bind_dist_equiv _ _ _ _)).symm,
--         end
--   },
--   {
--     simp [simulate_query, simulate'_query],
--     by_cases hs : s.is_fresh i t,
--     {
--       simp [hs],
--       sorry,
--     },
--     {
--       rw [not_is_fresh_iff_is_cached] at hs,
--       have : f ((s.lookup i t).get_or_else default, s) = s := sorry,
--       simp only [hs, this, get_or_else_of_is_cached],
--       sorry,
--     }
--   }


-- end

end cachingₛₒ

-- namespace sim_oracle

-- class is_resettable {S : Type} [has_bot S]
--   (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) :=
-- (apply_bind_fst_map_apply_dist_equiv (i i' : spec.ι) (t : spec.domain i) (t' : spec.domain i')
--   (s : S) : do {x ← so i' (t', s), fst <$> so' i (t, x.2)} ≃ₚ fst <$> so' i (t, s) )

-- instance cachingₛₒ_is_resettable : is_resettable (@cachingₛₒ spec) cachingₛₒ :=
-- {
--   apply_bind_fst_map_apply_dist_equiv := λ i i' t t' s,
--     cachingₛₒ.fst_map_apply_bind_apply_dist_equiv' _ _ _ _ _
-- }

-- class is_rewinding {S : Type} [preorder S]
--   (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) :=
-- (thing {α : Type} (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i)
--   (s : S) (f : α × S → S) (hf : ∀ (x : α × S), s ≤ x.2 → s ≤ f x ∧ f x ≤ x.2) :
--   (simulate so oa s >>= λ x, so' i (t, f x)) ≃ₚ so' i (t, s))

-- instance cachingₛₒ_is_rewindable : is_rewinding (@cachingₛₒ spec) cachingₛₒ :=
-- {
--   thing := begin
--     intros α oa i t s f hf,
--     induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t' generalizing s f hf,
--     {
--       simp [simulate_return],
--       refine trans (return_bind_dist_equiv _ _) _,
--       specialize hf (a, s) le_rfl,
--       have := le_antisymm hf.2 hf.1,
--       rw [this],
--     },
--     {
--       calc (simulate cachingₛₒ (oa >>= ob) s >>= λ y, cachingₛₒ i (t, f y)) ≃ₚ
--         (simulate cachingₛₒ oa s >>= λ x,
--           simulate cachingₛₒ (ob x.1) x.2) >>= λ y,
--           cachingₛₒ i (t, f y) : by pairwise_dist_equiv
--         ... ≃ₚ simulate cachingₛₒ oa s >>= λ x,
--           simulate cachingₛₒ (ob x.1) x.2 >>= λ y,
--           cachingₛₒ i (t, f y) : by pairwise_dist_equiv
--         ... ≃ₚ simulate cachingₛₒ oa s >>= λ x,
--           cachingₛₒ i (t, x.2) : begin
--             refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, _),
--             refine hob x.1 x.2 f _,
--             sorry,
--           end
--         ... ≃ₚ cachingₛₒ i (t, s) : begin
--           refine hoa s prod.snd (λ x h, ⟨h, le_rfl⟩),
--         end
--     },
--     {
--       simp only [simulate_query, cachingₛₒ.apply_eq],
--       by_cases h : s.is_fresh i' t',
--       {
--         rw [get_or_else_of_is_fresh _ _ h],
--         refine trans (bind_map_dist_equiv _ _ _) _,
--         by_cases hi : i = i',
--         {
--           induction hi,
--           sorry,
--         },
--         {
--           refine trans (bind_dist_equiv_right _ _ default _) _,
--           sorry, sorry,
--         }
--       },
--       {
--         obtain ⟨u, hu⟩ := lookup_eq_some_of_is_cached _ (is_cached_of_not_is_fresh _ h),
--         rw [get_or_else_of_lookup_eq_some _ _ hu],
--         refine trans (return_bind_dist_equiv _ _) _,
--         specialize hf (u, s) le_rfl,
--         have := le_antisymm hf.2 hf.1,
--         rw [this],
--       }
--     }
--   end,
-- }

-- end sim_oracle
