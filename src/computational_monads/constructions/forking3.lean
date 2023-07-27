/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.option
import computational_monads.asymptotics.queries_at_most
import computational_monads.simulation_semantics.query_store.basic

/-!
# Forking a Computation at a Query

Simpler formulation of forking lemma
-/

namespace oracle_comp

open oracle_spec

structure forking_adversary {spec : oracle_spec} (α : Type) (i : spec.ι) (q : ℕ) :=
(adv : oracle_comp spec α)
(choose_fork : α → option (spec.domain i))
(adv_queries_at_most : queries_at_most i adv q)

variables {spec : oracle_spec} {α β γ : Type} {i : spec.ι} {q : ℕ}

namespace forking_adversary

def run_fork (adversary : forking_adversary α i q) : oracle_comp spec (α × α) :=
do {
  x ← adversary.adv,
  x' ← adversary.adv,
  return (x, x')
}

end forking_adversary

end oracle_comp