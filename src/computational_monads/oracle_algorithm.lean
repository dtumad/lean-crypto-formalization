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

def unif_oracle := oracle_spec.uniform_selecting

open oracle_comp oracle_spec

variables {alg_spec : oracle_spec} {α β γ : Type}

structure oracle_algorithm (alg_spec : oracle_spec) :=
(base_S : Type) -- Oracle state when simulating computations
(base_sim_oracle : sim_oracle alg_spec uniform_selecting base_S)

namespace oracle_algorithm

section exec

/-- Use the algorithm's simulation oracle to run a computation. -/
noncomputable def exec (alg : oracle_algorithm alg_spec)
  (oa : oracle_comp alg_spec α) : oracle_comp unif_oracle α :=
dsimulate' alg.base_sim_oracle oa

variable (alg : oracle_algorithm alg_spec)

lemma exec_return_dist_equiv (a : α) :
  alg.exec (return' !alg_spec! a) ≃ₚ return' !unif_oracle! a :=
by pairwise_dist_equiv --simulate'_return_dist_equiv' _ _ _

end exec

end oracle_algorithm

/-- Can be used to default the simulation oracle in cases with no extra oracles. -/
noncomputable def base_oracle_algorithm :
  oracle_algorithm uniform_selecting :=
{ base_S := unit, base_sim_oracle := idₛₒ }

namespace base_oracle_algorithm

@[simp] lemma exec_eq (oa : oracle_comp uniform_selecting α) :
  base_oracle_algorithm.exec oa = oa :=
begin
  simp [oracle_algorithm.exec, base_oracle_algorithm],
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa,
  {
    simp [simulate'_return],
  },
  {
    simp [simulate'_bind, simulate_query,
      identity_oracle.apply_eq, mprod.def],
    rw [bind_assoc],
    simp_rw [return_bind],
    congr' 1,
    refine funext (λ u, _),
    specialize hoa u,
    exact hoa,
  }
end

end base_oracle_algorithm