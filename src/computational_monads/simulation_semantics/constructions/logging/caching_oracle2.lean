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
open_locale ennreal

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

lemma helper2 (i : spec.ι) (t : spec.domain i) (cache : query_cache spec)
  (oa : oracle_comp spec α) :
  do {x ← cachingₛₒ i (t, cache), simulate cachingₛₒ oa x.2} ≃ₚ
    do {x ← simulate cachingₛₒ oa cache, y ← cachingₛₒ i (t, x.2), return (x.1, y.2)} :=
begin
  induction oa

  -- by_cases ht : cache.is_fresh i t,
  -- {
  --   simp [ht],
  --   refine trans (bind_map_dist_equiv _ _ _) _,
  --   simp [function.comp],
  -- }
end

end cachingₛₒ

namespace sim_oracle

lemma test {S : Type} [partial_order S]
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S)
  (oa : oracle_comp spec α)
  (u : α × α) (s : S) :
  ⁅= ⁆ ≤
  ⁅= u | do {x ← simulate so oa s, y ← simulate so' oa x.2, return (x.1, y.1)}⁆


class is_resettable {S : Type} [has_bot S]
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) :=
(apply_bind_fst_map_apply_dist_equiv (i i' : spec.ι) (t : spec.domain i) (t' : spec.domain i')
  (s : S) : do {x ← so i' (t', s), fst <$> so' i (t, x.2)} ≃ₚ fst <$> so' i (t, s) )

instance cachingₛₒ_is_resettable : is_resettable (@cachingₛₒ spec) cachingₛₒ :=
{
  apply_bind_fst_map_apply_dist_equiv := λ i i' t t' s,
    cachingₛₒ.fst_map_apply_bind_apply_dist_equiv' _ _ _ _ _
}

class is_rewinding {S : Type} [preorder S]
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) :=
(thing {α : Type} (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i)
  (s : S) (f : α × S → S) (hf : ∀ (x : α × S), s ≤ x.2 → s ≤ f x ∧ f x ≤ x.2) :
  (simulate so oa s >>= λ x, so' i (t, f x)) ≃ₚ so' i (t, s))
(thing2 {α : Type} (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i)
  (s : S) (f : spec.range i × S → S)
    (hf : ∀ (x : spec.range i × S), s ≤ x.2 → s ≤ f x ∧ f x ≤ x.2) :
  (so i (t, s) >>= λ x, simulate' so' oa (f x)) ≃ₚ simulate' so' oa s)

-- class is_rewinding' {S : Type} [preorder S]
--   (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) :=
-- (thing {α : Type} (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i)
--   (γ : Type) (oc : oracle_comp spec γ)
--   (s : S) (f : α × S → S) (hf : ∀ (x : α × S), s ≤ x.2 → s ≤ f x ∧ f x ≤ x.2) :
--   (so i (t, s) >>= λ x, simulate so' oa (f x)))


instance cachingₛₒ_is_rewindable : is_rewinding (@cachingₛₒ spec) cachingₛₒ :=
{
  thing := begin sorry,
    -- intros α oa i t s f hf,
    -- induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t' generalizing s f hf,
    -- {
    --   simp [simulate_return],
    --   refine trans (return_bind_dist_equiv _ _) _,
    --   specialize hf (a, s) le_rfl,
    --   have := le_antisymm hf.2 hf.1,
    --   rw [this],
    -- },
    -- {
    --   calc (simulate cachingₛₒ (oa >>= ob) s >>= λ y, cachingₛₒ i (t, f y)) ≃ₚ
    --     (simulate cachingₛₒ oa s >>= λ x,
    --       simulate cachingₛₒ (ob x.1) x.2) >>= λ y,
    --       cachingₛₒ i (t, f y) : by pairwise_dist_equiv
    --     ... ≃ₚ simulate cachingₛₒ oa s >>= λ x,
    --       simulate cachingₛₒ (ob x.1) x.2 >>= λ y,
    --       cachingₛₒ i (t, f y) : by pairwise_dist_equiv
    --     ... ≃ₚ simulate cachingₛₒ oa s >>= λ x,
    --       cachingₛₒ i (t, x.2) : begin
    --         refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, _),
    --         refine hob x.1 x.2 f _,
    --         sorry,
    --       end
    --     ... ≃ₚ cachingₛₒ i (t, s) : begin
    --       refine hoa s prod.snd (λ x h, ⟨h, le_rfl⟩),
    --     end
    -- },
    -- {
    --   simp only [simulate_query, cachingₛₒ.apply_eq],
    --   by_cases h : s.is_fresh i' t',
    --   {
    --     rw [get_or_else_of_is_fresh _ _ h],
    --     refine trans (bind_map_dist_equiv _ _ _) _,
    --     by_cases hi : i = i',
    --     {
    --       induction hi,
    --       sorry,
    --     },
    --     {
    --       refine trans (bind_dist_equiv_right _ _ default _) _,
    --       sorry, sorry,
    --     }
    --   },
    --   {
    --     obtain ⟨u, hu⟩ := lookup_eq_some_of_is_cached _ (is_cached_of_not_is_fresh _ h),
    --     rw [get_or_else_of_lookup_eq_some _ _ hu],
    --     refine trans (return_bind_dist_equiv _ _) _,
    --     specialize hf (u, s) le_rfl,
    --     have := le_antisymm hf.2 hf.1,
    --     rw [this],
    --   }
    -- }
  end,

  thing2 :=
  begin
    intros α oa i t s f hf,
    by_cases ht : s.is_fresh i t,
    {
      simp [ht],
      refine trans (bind_map_dist_equiv _ _ _) _,
      simp [function.comp],
      simp [function.comp, dist_equiv.ext_iff, prob_output_bind_eq_tsum,
        prob_output_query_eq_inv],
        sorry,
    }
    sorry,

  end
}

-- instance cachingₛₒ_is_rewindable' : is_rewinding' (@cachingₛₒ spec) cachingₛₒ :=
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
--   end
-- }

namespace is_rewinding

theorem simulate_bind_simulate'_dist_equiv_simulate' {S : Type} [partial_order S]
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) [hso : is_rewinding so so']
  (oa : oracle_comp spec α) (oc : oracle_comp spec γ) (s : S)
  (f : α × S → S) (hf : ∀ (x : α × S), s ≤ x.2 → s ≤ f x ∧ f x ≤ x.2) :
  do {x ← simulate so oa s, simulate' so' oc (f x)} ≃ₚ simulate' so' oc s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t' generalizing oc s,
  {
    simp [simulate_return],
    refine trans (return_bind_dist_equiv _ _) _,
    specialize hf (a, s) le_rfl,
    have := le_antisymm hf.2 hf.1,
    rw [this],
    },
  {

    calc (simulate so (oa >>= ob) s >>= λ x, simulate' so' oc (f x)) ≃ₚ
      (simulate so oa s >>= λ x,
        simulate so (ob x.1) x.2) >>= λ y,
        simulate' so' oc (f y) : by pairwise_dist_equiv
      ... ≃ₚ simulate so oa s >>= λ x,
        simulate so (ob x.1) x.2 >>= λ y,
        simulate' so' oc (f y) : by pairwise_dist_equiv
      ... ≃ₚ simulate so oa s >>= λ x, simulate' so' oc x.2 : begin

        refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, _),
        refine hob x.1 f oc x.2 _,
        intros y hy,
        specialize hf y,
        sorry,
      end
        --sorry --bind_dist_equiv_bind_of_dist_equiv_right' _ _ _ (λ x, hob x.1 oc)
      ... ≃ₚ simulate' so' oc s : begin
        refine hoa prod.snd oc s _,
        sorry,
      end,

  },
  {
    rw [simulate_query],
    have := hso.thing2 oc i' t' s f hf,
    exact this,

    -- induction oc using oracle_comp.induction_on with β b β γ ob oc hob hoc i t,
    -- {
    --   simp [simulate'_return],
    --   refine trans (map_bind_dist_equiv _ _ _).symm _,

    --   refine trans (fst_map_bind_return_dist_equiv _ _ _) _,
    --   refine trans (map_const_dist_equiv _ _) _,
    --   pairwise_dist_equiv,
    -- },
    -- {

    --   calc (so i' (t', s) >>= λ x, simulate' so' (ob >>= oc) (f x)) ≃ₚ
    --     so i' (t', s) >>= λ x,
    --       simulate so' ob (f x) >>= λ y,
    --       simulate' so' (oc y.1) y.2 : by pairwise_dist_equiv

    --     ... ≃ₚ so i' (t', s) >>= λ x,
    --       simulate' so' ob (f x) >>= λ y,
    --       simulate' so' (oc y) s : begin
    --         pairwise_dist_equiv 1,
    --       end

    --     ... ≃ₚ (so i' (t', s) >>= λ x,
    --       simulate' so' ob (f x)) >>= λ y,
    --       simulate' so' (oc y) (s) : sorry



    --     ... ≃ₚ simulate so' ob s >>= λ y,
    --       simulate' so' (oc y.1) y.2 : begin
    --         sorry,
    --       end

    --     ... ≃ₚ simulate' so' (ob >>= oc) s : by pairwise_dist_equiv
    -- },
    -- {
    --   simp only [simulate'_query],
    --   sorry,
    -- }
  }
end

end is_rewinding

-- namespace is_resettable

-- -- theorem simulate_bind_simulate'_dist_equiv_simulate'' {S : Type} [has_bot S]
-- --   (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) [hso : is_resettable so so']
-- --   (oa : oracle_comp spec α) (oc : oracle_comp spec γ) :
-- --   do {x ← simulate so oa ⊥, simulate' so' oc x.2} ≃ₚ simulate' so' oc ⊥ :=
-- -- begin
-- --   induction oc using oracle_comp.induction_on with β b β γ ob oc hob hoc i t,
-- --   {
-- --     calc (simulate so oa ⊥ >>= λ (x : α × S), fst <$> return (b, x.snd)) ≃ₚ
-- --       (simulate so oa ⊥ >>= λ (x : α × S), fst <$> return (b, ⊥)) : by pairwise_dist_equiv 1
-- --       ... ≃ₚ fst <$> return (b, ⊥) :
-- --         bind_const_dist_equiv (simulate so oa ⊥) (fst <$> return (b, (⊥ : S)))
-- --   },
-- --   {

-- --   }

-- -- end

-- -- #check 0 ≤ 1 ∧ 1 ≤ 2

theorem simulate_bind_simulate'_dist_equiv_simulate' {S : Type} [has_bot S]
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S) [hso : is_resettable so so']
  (oa : oracle_comp spec α) (oc : oracle_comp spec γ) (s : S) :
  do {x ← simulate so oa s, simulate' so' oc x.2} ≃ₚ simulate' so' oc s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t' generalizing oc s,
  { by pairwise_dist_equiv },
  {

    calc (simulate so (oa >>= ob) s >>= λ x, simulate' so' oc x.snd) ≃ₚ
      (simulate so oa s >>= λ x,
        simulate so (ob x.1) x.2) >>= λ y,
        simulate' so' oc y.2 : by pairwise_dist_equiv
      ... ≃ₚ simulate so oa s >>= λ x,
        simulate so (ob x.1) x.2 >>= λ y,
        simulate' so' oc y.2 : by pairwise_dist_equiv
      ... ≃ₚ simulate so oa s >>= λ x, simulate' so' oc x.2 : begin

        refine bind_dist_equiv_bind_of_dist_equiv_right' _ _ _ (λ x, _),
        specialize hob x.1 oc x.2,
        exact hob
      end
        --sorry --bind_dist_equiv_bind_of_dist_equiv_right' _ _ _ (λ x, hob x.1 oc)
      ... ≃ₚ simulate' so' oc s : hoa oc s,

  },
  {
    rw [simulate_query],
    induction oc using oracle_comp.induction_on with β b β γ ob oc hob hoc i t,
    {
      simp [simulate'_return],
      refine trans (map_bind_dist_equiv _ _ _).symm _,

      refine trans (fst_map_bind_return_dist_equiv _ _ _) _,
      refine trans (map_const_dist_equiv _ _) _,
      pairwise_dist_equiv,
    },
    {

      calc (so i' (t', s) >>= λ x, simulate' so' (ob >>= oc) x.snd) ≃ₚ
        so i' (t', s) >>= λ x,
          (simulate so' ob x.2 >>= λ y,
          simulate' so' (oc y.1) y.2) : by pairwise_dist_equiv

        ... ≃ₚ (so i' (t', s) >>= λ x,
          simulate so' ob x.2) >>= λ y,
          simulate' so' (oc y.1) y.2 : by pairwise_dist_equiv

        ... ≃ₚ (simulate so' ob s >>= λ y,
          so i' (t', y.2) >>= λ z, return (y.1, z.2)) >>= λ z',
          simulate' so' (oc z'.1) z'.2 : begin
            pairwise_dist_equiv 1,
            sorry,

          end

        ... ≃ₚ simulate so' ob s >>= λ y,
          so i' (t', y.2) >>= λ z,
          simulate' so' (oc y.1) z.2 : begin

            refine trans (bind_bind_dist_equiv_assoc _ _ _) _,
            pairwise_dist_equiv,
          end

        ... ≃ₚ simulate so ob s >>= λ y,
          so' i' (t', y.2) >>= λ z,
          simulate' so' (oc y.1) z.2 : begin
            pairwise_dist_equiv,
          end

        ... ≃ₚ simulate so ob s >>= λ y,
          (so' i' (t', y.2) >>= λ z,
          simulate' so' (oc y.1) z.2) : begin
            by pairwise_dist_equiv
          end

        ... ≃ₚ simulate so ob s >>= λ y,
          simulate' so' (oc y.1) y.2 : begin
            pairwise_dist_equiv 1,
            specialize hoc x.1 x.2,
            exact hoc,
          end

        ... ≃ₚ simulate' so' (ob >>= oc) s : by pairwise_dist_equiv
    },
    {
      exact hso.apply_bind_fst_map_apply_dist_equiv i i' t t' s,
    }
  }
end

section forking

variables {T U : Type}
  [inhabited U] [fintype U] [fintype T] [decidable_eq T] [decidable_eq U] [inhabited T]

noncomputable def fork' (adv : oracle_comp (T ↦ₒ U) α)
  (f : α × query_cache (T ↦ₒ U) → option T) :
  oracle_comp (T ↦ₒ U) (option (α × α × query_cache (T ↦ₒ U))) :=
do {
  x ← simulate cachingₛₒ adv ∅,
  y ← simulate cachingₛₒ adv (x.2.drop_query () ((f x).get_or_else default)),
  return (if f x = f y ∧ f x ≠ none then some (x.1, y.1, x.2) else none)
}


lemma small (adv : oracle_comp (T ↦ₒ U) α) (f : α × query_cache (T ↦ₒ U) → option T) :
  ⁅λ x, option.is_some x | f <$> simulate cachingₛₒ adv ∅⁆ ^ 2 / (fintype.card T) ≤
    ⁅λ x, option.is_some x | fork' adv f⁆ :=
calc ⁅λ x, option.is_some x | f <$> simulate cachingₛₒ adv ∅⁆ ^ 2 / (fintype.card T) =

  (∑' t, ⁅= some t | f <$> simulate cachingₛₒ adv ∅⁆) ^ 2 / (fintype.card T) : begin
    by rw [prob_event_is_some],
  end

  ... ≤ (∑' t, (⁅= some t | f <$> simulate cachingₛₒ adv ∅⁆ ^ 2)) / fintype.card T : sorry -- Jensen

  ... = (∑' t, ⁅= (some t, some t) | (f <$> simulate cachingₛₒ adv ∅) ×ₘ (f <$> simulate cachingₛₒ adv ∅)⁆) / fintype.card T :
    begin
      simp [pow_two],
    end

  ... = (∑' t, ⁅= (some t, some t) | do {x ← simulate cachingₛₒ adv ∅,
    y ← simulate cachingₛₒ adv ∅,
    return (f x, f y)}⁆) / fintype.card T :
      begin
        refine congr_arg (λ x, x / (fintype.card T : ℝ≥0∞)) (tsum_congr (λ t, _)),
        pairwise_dist_equiv,
        simp [product],
        sorry,

      end
  --------------------------------------------------


  ... = ∑' t, ⁅= (some t, some t) | do {x ← simulate cachingₛₒ adv ∅,
    y ← simulate cachingₛₒ adv (x.2.drop_query () ((f x).get_or_else default)),
    return (f x, f y)}⁆ : sorry

  ... = ∑' t, ⁅λ z, f z.1 = some t ∧ f z.2 = some t | do {x ← simulate cachingₛₒ adv ∅,
    y ← simulate cachingₛₒ adv (x.2.drop_query () ((f x).get_or_else default)),
    return (x, y)}⁆ : sorry

  ... = ⁅λ z, f z.1 = f z.2 ∧ f z.1 ≠ none | do {x ← simulate cachingₛₒ adv ∅,
    y ← simulate cachingₛₒ adv (x.2.drop_query () ((f x).get_or_else default)),
    return (x, y)}⁆ : begin
      sorry
    end

  ... = ⁅λ x, option.is_some x | do {x ← simulate cachingₛₒ adv ∅,
    y ← simulate cachingₛₒ adv (x.2.drop_query () ((f x).get_or_else default)),
    return (if f x = f y ∧ f x ≠ none then some (x.1, y.1, x.2) else none)}⁆ : begin
      simp [prob_event_bind_eq_tsum],
      refine tsum_congr (λ x, _),
      refine congr_arg (λ x, _ * x) _,
      refine tsum_congr (λ y, _),

      split_ifs with h1 h2 h3,

      { refl },
      { refine false.elim (h2 (option.is_some_some)) },
      { refine false.elim ((option.not_is_some_iff_eq_none.2 rfl) h3), },
      { refl }
    end

  ... = ⁅λ x, option.is_some x | fork' adv f⁆ : rfl

end forking


-- end is_resettable

end sim_oracle
