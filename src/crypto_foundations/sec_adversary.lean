/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.instances
import computational_monads.asymptotics.polynomial_queries
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable

/-!
# Adversary for Security Games
-/

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec} {i : spec.ι} {q : ℕ}

namespace oracle_comp

section sec_adversary

structure sec_adversary (spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp (spec) β)
(qb : (spec).query_count)
(qb_is_bound (x : α) : queries_at_most (run x) qb)

-- structure sec_adversary' (α β : Type) :=
-- (additional_oracles : oracle_spec)
-- (run : α → oracle_comp (uniform_selecting ++ spec) β)
-- (S : Type) (sim_additional : sim_oracle additional_oracles spec S)

end sec_adversary

end oracle_comp
