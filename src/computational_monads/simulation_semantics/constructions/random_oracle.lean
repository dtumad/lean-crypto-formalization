/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.caching_oracle
import computational_monads.simulation_semantics.constructions.uniform_oracle
import computational_monads.simulation_semantics.oracle_compose
import computational_monads.simulation_semantics.mask_state

/-!
# Random Oralces

This file defines a traditional cryptographic `random_oracle`,
an oracle that responds uniformly to new queries, and with the same value for repeat queries.
The definition is a composition of a `uniform_oracle` and a `caching_oracle`.
-/

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

/-- Oracle that responds uniformly at random to any new queries,
but returns the same result to subsequent oracle queries.
Masking is used to hide the irrelevent state of the `uniform_oracle` -/
noncomputable def random_oracle (spec : oracle_spec) :
  sim_oracle spec unif_spec (query_log spec) :=
(uniformₛₒ ∘ₛₒ cachingₛₒ).mask_state (equiv.prod_punit (query_log spec))

-- noncomputable def random_oracle' (spec : oracle_spec) :
--   sim_oracle spec unif_spec spec.query_log :=
-- (uniformₛₒ ∘ₛₒ (caching_oracle' spec)).mask_state (equiv.prod_punit _)

notation `randomₛₒ` := random_oracle _

namespace random_oracle

-- TODO

end random_oracle