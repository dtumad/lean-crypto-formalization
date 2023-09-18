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

/-!
# Adversary for Security Games
-/

namespace oracle_comp

open_locale ennreal big_operators
open oracle_spec

variables {α β γ : Type} {adv_spec exp_spec : oracle_spec} {S S' : Type}

/-- A security adversary `sec_adversary adv_spec α β` is a computation taking inputs of type `α`
and computing a result of type `β` using oracles specified by `adv_spec`. -/
structure sec_adversary (adv_spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp adv_spec β)
(qb : query_count adv_spec)

section has_sim_oracle

/-- `adv.has_sim_oracle γ exp_spec S` means that the adversary can be simulated with `exp_spec`
using secret information of type `γ` and internal state of type `S`. -/
class sec_adversary.has_sim_oracle (adv : sec_adversary adv_spec α β)
  (γ : Type) (exp_spec : oracle_spec) (S : Type) :=
(so : α × γ → sim_oracle adv_spec exp_spec S)

instance has_sim_oracle_self (adv : sec_adversary adv_spec α β) :
  adv.has_sim_oracle γ adv_spec unit := {so := λ _, idₛₒ}

def sec_adversary.so (adv : sec_adversary adv_spec α β) [h : adv.has_sim_oracle γ exp_spec S]
  (x : α × γ) : sim_oracle adv_spec exp_spec S := h.so x

end has_sim_oracle

-- def sec_adversary.simulate_run (adv : sec_adversary adv_spec α β) (x : α × γ) : oracle_comp exp_spec (β × S) :=
-- default_simulate (adv.so x) (adv.run x.1)

section sec_experiment

/-- A `sec_experiment exp_spec α β γ S` represents a security experiment for a `sec_adversary`,
where `α` is the input type to the adversary, `β` is the result type of the adversary,
`γ` is the secret information not shared with the adversary, and `S` is the simulation state. -/
structure sec_experiment (adv_spec exp_spec : oracle_spec) (α β γ S : Type) :=
(inp_gen : oracle_comp exp_spec (α × γ))
(so : α × γ → sim_oracle adv_spec exp_spec S)
(is_valid : α × γ → β × S → oracle_comp exp_spec bool)

end sec_experiment

section advantage

/-- `adv.advantage exp so` is the chance that `adv` succeeds in the experiment defined by `exp`
when simulated using `so`, assuming we start with the default state for `so`. -/
noncomputable def sec_adversary.advantage (adv : sec_adversary adv_spec α β)
  (exp : sec_experiment adv_spec exp_spec α β γ S)
  (so : sim_oracle exp_spec uniform_selecting S') : ℝ≥0∞ :=
⁅= tt | default_simulate' so
  (do {x ← exp.inp_gen, z ← default_simulate (exp.so x) (adv.run x.1), exp.is_valid x z})⁆

/-- version of `sec_adversary.advantage` where the initial input is fixed,
rather than being drawn from the input generator function. -/
noncomputable def sec_adversary.advantage_on_input (adv : sec_adversary adv_spec α β)
  (exp : sec_experiment adv_spec exp_spec α β γ S)
  (so : sim_oracle exp_spec uniform_selecting S') (x : α × γ) : ℝ≥0∞ :=
⁅= tt | default_simulate' so
  (do {z ← default_simulate (exp.so x) (adv.run x.1),
    exp.is_valid x z})⁆

end advantage

section base

@[inline, reducible] def base_sec_experiment (exp_spec : oracle_spec) (α β : Type) :=
sec_experiment exp_spec exp_spec α β unit unit

def base_sec_experiment_of_is_valid {exp_spec : oracle_spec} {α β : Type}
  (inp_gen : oracle_comp exp_spec α) (is_valid : α → β → oracle_comp exp_spec bool) :
  base_sec_experiment exp_spec α β :=
{ inp_gen := (λ x, (x, ())) <$> inp_gen,
  so := λ _, idₛₒ,
  is_valid := λ x y, is_valid x.1 y.1 }

/-- Version of `sec_adversary.advantage` when there is no "hidden" information or simulation state,
and where both the experiment and adversary use a common set of oracles. -/
noncomputable def sec_adversary.base_advantage (adv : sec_adversary adv_spec α β)
  (exp : base_sec_experiment adv_spec α β) : ℝ≥0∞ :=
adv.advantage exp uniformₛₒ

lemma base_advantage_eq_prob_output (adv : sec_adversary adv_spec α β)
  (exp : base_sec_experiment adv_spec α β) : adv.base_advantage exp =
    ⁅= tt | do {x ← exp.inp_gen, z ← default_simulate (exp.so x) (adv.run x.1), exp.is_valid x z}⁆ :=
by rw [sec_adversary.base_advantage, sec_adversary.advantage,
  uniform_oracle.prob_output_simulate']


end base

-- structure adversary_reduction (adv_spec₁ adv_spec₂ : oracle_spec) (α₁ β₁ α₂ β₂ : Type)
--   {exp_spec₁ exp_spec₂ : oracle_spec} {γ₁ γ₂ S₁ S₂} :=
-- (reduction : sec_adversary adv_spec₁ α₁ β₁ → sec_adversary adv_spec₂ α₂ β₂)

end oracle_comp
