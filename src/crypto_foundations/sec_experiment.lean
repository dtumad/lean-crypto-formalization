/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.instances
import computational_monads.asymptotics.polynomial_queries
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable
import computational_monads.simulation_semantics.constructions.identity_oracle
import computational_monads.simulation_semantics.constructions.uniform_oracle
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.mask_state

/-!
# Adversary for Security Games
-/

open oracle_comp oracle_spec
open_locale ennreal

structure sec_adversary (adv_spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp adv_spec β)
(qb : query_count adv_spec)

structure algorithm_base (spec : oracle_spec) :=
(S : Type) (so : sim_oracle spec uniform_selecting S)

structure sec_experiment (exp_spec : oracle_spec) (α β S : Type)
  extends algorithm_base exp_spec :=
(inp_gen : oracle_comp exp_spec α)
(run : α → oracle_comp exp_spec β)
(is_valid : α × β → Prop)

def algorithm_base.exec {spec : oracle_spec} {α : Type}
  (alg : algorithm_base spec) (oa : oracle_comp spec α) :
  oracle_comp uniform_selecting α :=
dsimulate' alg.so oa

def sec_experiment.run_experiment {spec : oracle_spec} {α β S : Type}
  (exp : sec_experiment spec α β S) :
  oracle_comp uniform_selecting (α × β)  :=
exp.exec (do
  { x ← exp.inp_gen,
    y ← exp.run x,
    return (x, y) } )

noncomputable def sec_experiment.advantage {spec : oracle_spec} {α β S : Type}
  (exp : sec_experiment spec α β S) : ℝ≥0∞ :=
⁅exp.is_valid | exp.run_experiment⁆