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

/-- A security adversary `sec_adversary adv_spec α β` is a computation taking inputs of type `α`
and computing a result of type `β` using oracles specified by `adv_spec`. -/
structure sec_adversary (adv_spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp adv_spec β)

section has_sim_oracle

/-- `adv.has_sim_oracle γ exp_spec S` means that the adversary can be simulated with `exp_spec`
using secret information of type `γ` and internal state of type `S`. -/
class sec_adversary.has_sim_oracle (adv : sec_adversary adv_spec α β)
  (γ : Type) (exp_spec : oracle_spec) (S : Type) :=
(so : γ → sim_oracle adv_spec exp_spec S)

instance has_sim_oracle_self (adv : sec_adversary adv_spec α β) :
  adv.has_sim_oracle γ adv_spec unit := {so := λ _, idₛₒ}

def sec_adversary.so (adv : sec_adversary adv_spec α β) [h : adv.has_sim_oracle γ exp_spec S]
  (g : γ) : sim_oracle adv_spec exp_spec S := h.so g

end has_sim_oracle

section sec_experiment

/-- A `sec_experiment exp_spec α β γ S` represents a security experiment for a `sec_adversary`,
where `α` is the input type to the adversary, `β` is the result type of the adversary,
`γ` is the secret information not shared with the adversary, and `S` is the simulation state. -/
structure sec_experiment (exp_spec : oracle_spec) (α β γ S : Type) :=
(run : sec_adversary adv_spec α β → oracle_comp exp_spec bool)
(inp_gen : oracle_comp exp_spec (α × γ))
(is_valid : α × β × S → oracle_comp exp_spec bool)
(exp_so : sim_oracle exp_spec uniform_selecting unit)

end sec_experiment

section advantage

noncomputable def sec_adversary.advantage (adv : sec_adversary adv_spec α β)
  (exp : sec_experiment exp_spec α β γ S) [adv.has_sim_oracle γ exp_spec S] : ℝ≥0∞ :=
⁅= tt | default_simulate' exp.exp_so
  (do {(x, y) ← exp.inp_gen,
    z ← default_simulate (adv.so y) (adv.run x),
    exp.is_valid (x, z)})⁆

noncomputable def sec_adversary.advantage_on_input (adv : sec_adversary adv_spec α β)
  (exp : sec_experiment exp_spec α β γ S) [adv.has_sim_oracle γ exp_spec S]
  (x : α) (secret : γ) : ℝ≥0∞ :=
⁅= tt | do {z ← default_simulate (adv.so secret) (adv.run x),
  exp.is_valid (x, z)}⁆

end advantage

end oracle_comp
