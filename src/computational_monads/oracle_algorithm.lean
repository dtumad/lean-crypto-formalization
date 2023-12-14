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

def unif_oracle := oracle_spec.unif_spec

open oracle_comp oracle_spec

variables {alg_spec : oracle_spec} {α β γ : Type}

structure oracle_algorithm (alg_spec : oracle_spec) :=
(base_S : Type) -- Oracle state when simulating computations
(init_state : base_S) -- Initial state for the oracle
(base_sim_oracle : sim_oracle alg_spec unif_spec base_S)

namespace oracle_algorithm

section exec

/-- Use the algorithm's simulation oracle to run a computation. -/
def exec (alg : oracle_algorithm alg_spec)
  (oa : oracle_comp alg_spec α) : oracle_comp unif_oracle α :=
simulate' alg.base_sim_oracle oa alg.init_state

variables (alg : oracle_algorithm alg_spec)

@[simp] lemma exec_return (a : α) :
  alg.exec (return' !alg_spec! a) = return' !unif_oracle! a := rfl

@[simp] lemma exec_bind (oa : oracle_comp alg_spec α) (ob : α → oracle_comp alg_spec β) :
  alg.exec (oa >>= ob) = (simulate alg.base_sim_oracle oa alg.init_state) >>=
    λ z, (simulate' alg.base_sim_oracle (ob z.1) z.2) :=
simulate'_bind _ _ _ _

@[simp] lemma exec_query (i : alg_spec.ι) (t : alg_spec.domain i) :
  alg.exec (query i t) = prod.fst <$> alg.base_sim_oracle i (t, alg.init_state) :=
simulate'_query _ _ _ _

@[simp] lemma map_exec (f : α → β) (oa : oracle_comp alg_spec α) :
  f <$> (alg.exec oa) = alg.exec (f <$> oa) :=
by simp_rw [exec, simulate'_map]

end exec

end oracle_algorithm

/-- Can be used to default the simulation oracle in cases with no extra oracles. -/
def base_oracle_algorithm : oracle_algorithm unif_spec :=
{ base_S := unit, init_state := (),
  base_sim_oracle := idₛₒ }

namespace base_oracle_algorithm

@[simp] lemma exec_eq (oa : oracle_comp unif_spec α) :
  base_oracle_algorithm.exec oa = oa :=
identity_oracle.simulate'_eq_self oa ()

end base_oracle_algorithm