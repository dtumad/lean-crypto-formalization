/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.identity_oracle

/-!
# Base Structure for Algorithms With Oracle Access

This file defines a `oracle_algorithm` structure as a base for building more general algorithms.
The motivation is to define structures like an encryption or signing algorithms,
while remaining agnostic to the presence of e.g. a random oracle.

The structure `oracle_algorithm spec` on its own only contains a `sim_oracle` specifying intended
semantics of the globally available oracles, and is meant to be extended with further functions
representing the actual algorithms themselves.
-/

open oracle_comp oracle_spec

structure oracle_algorithm (alg_spec : oracle_spec) :=
(base_S : Type) -- Oracle state when simulating computations
(base_sim_oracle : sim_oracle alg_spec uniform_selecting base_S)

namespace oracle_algorithm

variables {alg_spec : oracle_spec} (alg : oracle_algorithm alg_spec)

def unif_oracle := uniform_selecting

section exec

noncomputable def exec (alg : oracle_algorithm alg_spec) {α : Type}
  (oa : oracle_comp alg_spec α) : oracle_comp unif_oracle α :=
dsimulate' alg.base_sim_oracle oa

section return

variables {α : Type} (a : α)

@[pairwise_dist_equiv] lemma exec_return_dist_equiv :
  alg.exec (return' !alg_spec! a) ≃ₚ return' !unif_oracle! a :=
simulate'_return_dist_equiv' _ _ _




end return

end exec

end oracle_algorithm