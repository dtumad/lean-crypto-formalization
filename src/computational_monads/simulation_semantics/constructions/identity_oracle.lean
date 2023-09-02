/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_stateless

/-!
# Identity Simulation Oracle

This file defines a stateless simulation oracle `identity_oracle spec`, denoted `idₛₒ`, that
simulates a computation by making no changes (equivalently replacing queries with themselves).
This is mainly useful when appending simulation oracles and only simulating some of them.
-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- Simulation oracle for preserving the current oracle queries as is.
Can be combined with other simulation oracles to preserve some subset of queries,
e.g. `so ++ₛₒ idₛₒ` will simulate the left side oracles and preserve right side oracles. -/
@[inline, reducible]
def identity_oracle (spec : oracle_spec) : sim_oracle spec spec unit := ⟪query⟫

notation `idₛₒ` := identity_oracle _

instance identity_oracle.is_stateless : (identity_oracle spec).is_stateless :=
stateless_oracle.is_stateless query

namespace identity_oracle

variables (oa : oracle_comp spec α) (s : unit)

-- TODO

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' idₛₒ oa s ≃ₚ oa :=
sim_oracle.is_tracking.simulate'_dist_equiv_self idₛₒ oa s
  (λ i t, stateless_oracle.answer_query_dist_equiv _ _)

@[pairwise_dist_equiv] lemma simulate_dist_equiv : simulate idₛₒ oa s ≃ₚ (oa ×ₘ return ()) :=
sim_oracle.is_stateless.simulate_dist_equiv_self idₛₒ oa s
  (λ i t, stateless_oracle.answer_query_dist_equiv _ _)

end identity_oracle