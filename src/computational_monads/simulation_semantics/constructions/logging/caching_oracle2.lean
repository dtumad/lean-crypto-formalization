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
open_locale ennreal big_operators classical -- TODO: temp classical (maybe we should have this for all dist sem)

variables {α β γ δ : Type} {spec spec' : oracle_spec}

/-- Oracle for tracking previous queries, and returning the same value for matching inputs.
The `query_cache.get_or_else` function allows us to run a fallback for non-cached values. -/
def cachingₛₒ {spec : oracle_spec} : sim_oracle spec spec (query_cache spec) :=
{ default_state := ∅,
  o := λ i ⟨t, cache⟩, cache.get_or_else i t (query i t) }

namespace cachingₛₒ

@[simp] lemma apply_eq (i : spec.ι) (x : spec.domain i × query_cache spec) :
  cachingₛₒ i x = x.2.get_or_else i x.1 (query i x.1) := by cases x; refl

/-- Simulation with a caching oracle will only ever grow the cash and doesn't remove elements. -/
lemma le_of_mem_support_simulate (oa : oracle_comp spec α) (cache : query_cache spec) :
  ∀ z ∈ (simulate cachingₛₒ oa cache).support, cache ≤ snd z :=
begin
  intros z hz,
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing cache,
  { rw [mem_support_simulate_return_iff] at hz,
    exact hz.2 ▸ le_rfl },
  { rw [mem_support_simulate_bind_iff] at hz,
    obtain ⟨x, s, hs, hzx⟩ := hz,
    exact (hoa (x, s) cache hs).trans (hob x z s hzx) },
  { exact cache.le_of_mem_support_get_or_else z hz }
end

/-- Probability of getting to a final result given a partial cache for queries is given by
the product of probabilities that each additional query gets the expected result.
Note that this requires `z` be in the support of the simulation (as the empty product is `1`). -/
lemma finite_version (oa : oracle_comp spec α) (cache : query_cache spec)
  (z : α × query_cache spec) (hz : z ∈ (simulate cachingₛₒ oa cache).support) :
  ⁅= z | simulate cachingₛₒ oa cache⁆ =
    ∏ i in (z.2.cached_inputs \ cache.cached_inputs), (fintype.card $ spec.range i.1)⁻¹ :=
begin
  have : cache ≤ z.2 := le_of_mem_support_simulate oa cache z hz,
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

/-- The possible outputs of simulating a computation with a larger initial cache is
at most the original set of possible outputs (although the possible final caches may differ). -/
lemma support_antitone' (oa : oracle_comp spec α) (s s' : query_cache spec)
  (hs : s ≤ s') : (simulate' cachingₛₒ oa s').support ⊆ (simulate' cachingₛₒ oa s).support :=
begin

  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s s',
  {
    -- rw [simulate_return, simulate_return],
    simp,
  },
  sorry,
  sorry,
end

lemma mem_support_of_le_mem_support (oa : oracle_comp spec α) (s₀ s : query_cache spec)
  (hs : s₀ ≤ s) (z : α × query_cache spec) (hzs : s ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  z ∈ (simulate cachingₛₒ oa s).support :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing,
  {
    -- rw [simulate_return, simulate_return],
    simp at hz,
    simp [hz, prod.eq_iff_fst_eq_snd_eq] at hzs ⊢,
    refine le_antisymm hs hzs,
  },
  {
    sorry,
  },
  {
    simp [simulate_query] at hz ⊢,
    -- TODO: helper lemma
    by_cases hs₀ : s₀.is_fresh i t,
    {
      rw [mem_support_get_or_else_iff_of_is_fresh _ _ hs₀] at hz,
      rw [← hz.2] at hzs,
      sorry,
    },
    sorry,
  }
end

/-- Given a pair of caches `s ≤ s'`, such that some result `z` is possible in both simulations,
the probability of getting that result is higher when starting with the larger cache,
since it has fewer additional choices at which it could diverge from calculating `z`. -/
lemma prob_output_monotone (oa : oracle_comp spec α) (s s' : query_cache spec)
  (hs : s ≤ s') (z : α × query_cache spec)
  (hz' : z ∈ (simulate cachingₛₒ oa s').support) :
  ⁅= z | simulate cachingₛₒ oa s⁆ ≤ ⁅= z | simulate cachingₛₒ oa s'⁆ :=
begin
  by_cases hz : z ∈ (simulate cachingₛₒ oa s).support,
  {
    rw [finite_version _ _ _ hz', finite_version _ _ _ hz],
    sorry,
  },
  {
    simp only [hz, prob_output_eq_zero, not_false_iff, zero_le'],
  }
end


----- FORKING MAP BELOW
structure forking_map (α : Type) (s₀ : query_cache spec) :=
(to_fun : α × query_cache spec → query_cache spec)
(le_to_fun (z : α × query_cache spec) : s₀ ≤ to_fun z)
(to_fun_le (z : α × query_cache spec) : to_fun z ≤ z.2)

def forking_map.to_fun₂ (s₀ : query_cache spec) (f : forking_map α s₀) :
  α × query_cache spec → α × query_cache spec :=
λ z, (z.1, f.to_fun z)

/-- Given a pair of caches `s ≤ s'`, such that some result `z` is possible in both simulations,
the probability of getting that result is higher when starting with the larger cache,
since it has fewer additional choices at which it could diverge from calculating `z`. -/
lemma prob_output_monotone' (oa : oracle_comp spec α) (s₀ : query_cache spec)
  (f : α × query_cache spec → query_cache spec) (hf : ∀ z, s₀ ≤ f z ∧ f z ≤ z.2)
  (z' : α × query_cache spec) :
  ⁅= z' | do {z ← simulate cachingₛₒ oa s₀, return (z.1, f z)}⁆ ≤
    ⁅= z' | do {z ← simulate cachingₛₒ oa z'.2, return (z.1, f z)}⁆ :=
begin
  rw [prob_output_bind_return_eq_tsum,
    prob_output_bind_return_eq_tsum],
  refine ennreal.tsum_le_tsum (λ z, _),
  split_ifs with hz,
  {
    simp [hz],
    by_cases hzs : z ∈ (simulate cachingₛₒ oa s₀).support,
    {
      apply prob_output_monotone,
      {
        exact (hf z).1,
      },
      {
        refine mem_support_of_le_mem_support oa s₀ (f z) (hf z).1 z (hf z).2 hzs,
      }
    },
    {
      simp [hzs],
    }

  },
  {
    refine le_rfl,
  }
end


lemma prob_output_eq_le_prob_output_eq_rewind
  (oa : oracle_comp spec α) (s₀ : query_cache spec) (x : α)
  (f : α × query_cache spec → query_cache spec)
  (hf : ∀ z, s₀ ≤ f z ∧ f z ≤ z.2) :

  let loss_factor : ℝ≥0∞ := ↑(f <$> simulate cachingₛₒ oa s₀).fin_support.card in
  ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 / loss_factor ≤
    ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
      z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ :=

let loss_factor : ℝ≥0∞ := ↑(f <$> simulate cachingₛₒ oa s₀).fin_support.card in
-- First switch to a sum over the possible intermediate values `sf` that will be chosen by `f`.
calc ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 / loss_factor =
    (∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
      ⁅= (x, sf) | do {z ← simulate cachingₛₒ oa s₀, return (z.1, f z)}⁆) ^ 2 / loss_factor :
  begin
    sorry
  end
-- Use the loss factor to bring the square inside the summation.
... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= (x, sf) | do {z ← simulate cachingₛₒ oa s₀, return (z.1, f z)}⁆ ^ 2 :
  begin
    have := ennreal.pow_sum_div_card_le_sum_pow (f <$> simulate cachingₛₒ oa s₀).fin_support
      (λ sf, ⁅= (x, sf) | simulate cachingₛₒ oa s₀ >>= λ z, return (z.1, f z)⁆) (λ _ _, prob_output_ne_top _ _) 1,
    simpa only [pow_one, one_add_one_eq_two] using this
  end

-- Substitute probability for running the computation twice in sequence.
... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= ((x, sf), (x, sf)) | (λ (z : α × query_cache spec), (prod.fst z, f z)) <$> (simulate cachingₛₒ oa s₀)
          ×ₘ (λ (z : α × query_cache spec), (prod.fst z, f z)) <$> (simulate cachingₛₒ oa s₀)⁆ :
  begin
    refine finset.sum_congr rfl (λ sf hsf, _),
    rw [prob_output_product, pow_two],
    refl,
  end
-- Substitute probability for running the computation twice in sequence.
... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
          z' ← simulate cachingₛₒ oa s₀, return ((z.1, f z), (z'.1, f z'))}⁆ :
  begin
    refine finset.sum_congr rfl (λ sf hsf, _),
    sorry,
  end
-- Run second computation from the intermediate cache `sf` instead of the base cache `s₀`.
... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
  ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
    z' ← simulate cachingₛₒ oa sf, return ((z.1, f z), (z'.1, f z'))}⁆ :
  begin
    sorry,
  end
-- Substitute the value `sf` for `f z`, which is equal assuming the probability is non-zero.
... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
          z' ← simulate cachingₛₒ oa (f z), return ((z.1, f z), (z'.1, f z'))}⁆ :
  begin
    sorry
  end
-- Improve total probability by just not checking what the second cache returned is.
... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= ((x, sf), x) | do {z ← simulate cachingₛₒ oa s₀,
          z' ← simulate cachingₛₒ oa (f z), return ((z.1, f z), z'.1)}⁆ :
  begin
    sorry
  end
-- Revert the summation over the intermediate cache values.
... = ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
        z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ :
  begin
    sorry
  end







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

end cachingₛₒ
