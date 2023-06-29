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

end cachingₛₒ

namespace sim_oracle

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

instance cachingₛₒ_is_rewindable : is_rewinding (@cachingₛₒ spec) cachingₛₒ :=
{
  thing := begin
    intros α oa i t s f hf,
    induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t' generalizing s f hf,
    {
      simp [simulate_return],
      refine trans (return_bind_dist_equiv _ _) _,
      specialize hf (a, s) le_rfl,
      have := le_antisymm hf.2 hf.1,
      rw [this],
    },
    {
      calc (simulate cachingₛₒ (oa >>= ob) s >>= λ y, cachingₛₒ i (t, f y)) ≃ₚ
        (simulate cachingₛₒ oa s >>= λ x,
          simulate cachingₛₒ (ob x.1) x.2) >>= λ y,
          cachingₛₒ i (t, f y) : by pairwise_dist_equiv
        ... ≃ₚ simulate cachingₛₒ oa s >>= λ x,
          simulate cachingₛₒ (ob x.1) x.2 >>= λ y,
          cachingₛₒ i (t, f y) : by pairwise_dist_equiv
        ... ≃ₚ simulate cachingₛₒ oa s >>= λ x,
          cachingₛₒ i (t, x.2) : begin
            refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, _),
            refine hob x.1 x.2 f _,
            sorry,
          end
        ... ≃ₚ cachingₛₒ i (t, s) : begin
          refine hoa s prod.snd (λ x h, ⟨h, le_rfl⟩),
        end
    },
    {
      simp only [simulate_query, cachingₛₒ.apply_eq],
      by_cases h : s.is_fresh i' t',
      {
        rw [get_or_else_of_is_fresh _ _ h],
        refine trans (bind_map_dist_equiv _ _ _) _,
        by_cases hi : i = i',
        {
          induction hi,
          sorry,
        },
        {
          refine trans (bind_dist_equiv_right _ _ default _) _,
          sorry, sorry,
        }
      },
      {
        obtain ⟨u, hu⟩ := lookup_eq_some_of_is_cached _ (is_cached_of_not_is_fresh _ h),
        rw [get_or_else_of_lookup_eq_some _ _ hu],
        refine trans (return_bind_dist_equiv _ _) _,
        specialize hf (u, s) le_rfl,
        have := le_antisymm hf.2 hf.1,
        rw [this],
      }
    }
  end,
}

end sim_oracle
