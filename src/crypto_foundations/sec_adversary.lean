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

/-!
# Adversary for Security Games
-/

namespace oracle_comp

open_locale ennreal big_operators
open oracle_spec

variables {α β γ : Type} {adv_spec exp_spec : oracle_spec} {S : Type}

structure sec_adversary (adv_spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp adv_spec β)

class sec_adversary.has_sim_oracle (adv : sec_adversary adv_spec α β)
  (exp_spec : oracle_spec) (S : Type) :=
(so : sim_oracle adv_spec exp_spec S)

instance has_sim_oracle_self (adv : sec_adversary adv_spec α β) :
  adv.has_sim_oracle adv_spec unit := {so := idₛₒ}

def sec_adversary.so (adv : sec_adversary adv_spec α β) [h : adv.has_sim_oracle exp_spec S] :
  sim_oracle adv_spec exp_spec S := h.so

structure sec_experiment (exp_spec : oracle_spec) (α β S : Type) :=
(inp_gen : oracle_comp exp_spec α)
(is_valid : β × S → oracle_comp exp_spec bool)

-- def sec_experiment := β × S → oracle_comp exp_spec bool

noncomputable def sec_adversary.advantage (adv : sec_adversary adv_spec α β)
  (exp : sec_experiment exp_spec α β S) [adv.has_sim_oracle exp_spec S] : ℝ≥0∞ :=
⁅= tt | do {(x : α) ← exp.inp_gen, z ← default_simulate adv.so (adv.run x), exp.is_valid z}⁆

-- variable (adv : sec_adversary adv_spec exp_spec α β S)

-- def sec_adversary.simulate_run (x : α) (s : S) :
--   oracle_comp exp_spec (β × S) := simulate adv.so (adv.run x) s

-- @[inline, reducible] def sec_adversary.default_simulate_run
--   (x : α) : oracle_comp exp_spec (β × S) := adv.simulate_run x adv.so.default_state

-- section sec_adversary

-- structure sec_adversary (spec : oracle_spec) (α β : Type) :=
-- (run : α → oracle_comp (spec) β)
-- (qb : (spec).query_count)
-- (qb_is_bound (x : α) : queries_at_most (run x) qb)

-- end sec_adversary

end oracle_comp
