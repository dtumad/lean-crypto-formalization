/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.query_tracking.query_log.basic

/-!
# Caching Simulation Oracle

This file defines a `sim_oracle` that implements caching functionality.
`cachingₛₒ` represents a simulator that caches fresh queries and returns the same value
for any future queries, using a `query_log` as an internal state for tracking this.

This is used by being composed with other oracles, such as in `random_oracle`.

-- TODO: a lot of this isn't quite right and not needed for fork.
-/

open oracle_comp oracle_spec
open prod (fst) (snd)
open_locale ennreal big_operators classical -- TODO: temp classical (maybe we should have this for all dist sem)

variables {α β γ δ : Type} {spec spec' : oracle_spec}

/-- Oracle for tracking previous queries, and returning the same value for matching inputs. -/
def caching_oracle (spec : oracle_spec) : sim_oracle spec spec (query_log spec) :=
λ i ⟨t, cache⟩, cache.lookup_or_query i t

notation `cachingₛₒ` := caching_oracle _

namespace caching_oracle

section apply

@[simp] lemma apply_eq (i : spec.ι) (z : spec.domain i × query_log spec) :
  cachingₛₒ i z = z.2.lookup_or_query i z.1 := by cases z; refl

variables {i : spec.ι} {z : spec.domain i × query_log spec}
  {t : spec.domain i} {s₀ : query_log spec}

end apply

end caching_oracle
