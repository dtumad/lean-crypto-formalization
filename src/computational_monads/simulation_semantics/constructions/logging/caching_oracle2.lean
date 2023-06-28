/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.query_cache.get_or_else
import computational_monads.simulation_semantics.simulate.monad

/-!
# Caching Simulation Oracle

This file defines a `sim_oracle` that implements caching functionality.
`cachingₛₒ` represents a simulator that caches fresh queries and returns the same value
for any future queries, using a `query_cache` as an internal state for tracking this.

This is used by being composed with other oracles, such as in `random_oracle`.
-/

open oracle_comp oracle_spec query_cache
open prod (fst) (snd)

variables {α β γ δ : Type} {spec spec' : oracle_spec}

/-- Oracle for logging previous queries, and returning the same value for matching inputs.
The `query_cache.get_or_else` function allows us to run a fallback for non-cached values. -/
def cachingₛₒ {spec : oracle_spec} : sim_oracle spec spec (query_cache spec) :=
{ default_state := ∅,
  o := λ i ⟨t, cache⟩, cache.get_or_else i t (query i t) }

namespace caching_oracle

@[simp] lemma apply_eq (i : spec.ι) (x : spec.domain i × query_cache spec) :
  cachingₛₒ i x = x.2.get_or_else i x.1 (query i x.1) := by cases x; refl

@[simp_dist_equiv] lemma fst_map_apply_bind_apply_dist_equiv'
  (i : spec.ι) (t : spec.domain i) (i' : spec.ι) (t' : spec.domain i') (cache : query_cache spec) :
  do {x ← cachingₛₒ i' (t', cache), fst <$> cachingₛₒ i (t, x.2)} ≃ₚ
    fst <$> cachingₛₒ i (t, cache) :=
begin
  refine trans (by apply fst_map_get_or_else_bind_get_or_else_dist_equiv) _,
  split_ifs with hi ht,
  induction hi,
  simp [← ht],
  pairwise_dist_equiv,
  pairwise_dist_equiv,
end

end caching_oracle
