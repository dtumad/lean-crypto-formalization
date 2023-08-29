/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.instances
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.simulation_semantics.constructions.seeded_oracle
import computational_monads.asymptotics.queries_at_most

/-!
# Adversary for Security Games
-/

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec} {i : spec.ι} {q : ℕ}

namespace oracle_comp

section sec_adversary

structure sec_adversary (spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp (uniform_selecting ++ spec) β)
-- TODO: poly_time
(qb : (uniform_selecting ++ spec).query_count)
(qb_is_bound (x : α) : queries_at_most (run x) qb)

end sec_adversary

end oracle_comp
