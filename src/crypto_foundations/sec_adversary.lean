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

/-- A security adversary `sec_adversary adv_spec α β` is a computation taking inputs of type `α`
and computing a result of type `β` using oracles specified by `adv_spec`. -/
structure sec_adversary (adv_spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp adv_spec β)
(qb : query_count adv_spec)

/-- A `soundness_experiment exp_spec α β S` is a experiment for the correctness of a cryptographic
algorithm, in order to check that a property always (or almost always) holds for an algorithm.
`α` is the type returned by the input generator, `β` is the result of the psuedo-adversary,
and `exp_spec` is the set of oracles in the experiment with `S` the internal state in simulation.
For example `α` may be a pair of fairly generated encryption keys and `β` the possible messages,
with `inp_gen` choosing the keys from a key generation function, and the adversary attempting
to return a message that fails to decrypt properly after encryption (as checked by `is_valid`). -/
structure soundness_experiment (exp_spec : oracle_spec) (α β S : Type) :=
(inp_gen : oracle_comp exp_spec α)
(is_valid : α → β → oracle_comp exp_spec bool)
(exp_so : sim_oracle exp_spec (uniform_selecting ++ ∅) S)

/-- A `sec_experiment adv_spec exp_spec α β γ S S'` is a security experiment for a `sec_adversary`,
where `α` is the input type to the adversary, `β` is the result type of the adversary,
`γ` is the secret information not shared with the adversary, `S` is the adversary simulation state,
and `S'` is the experiment simulation state (which isn't used in practice). -/
structure sec_experiment (adv_spec exp_spec : oracle_spec) (α β γ S S' : Type) :=
(inp_gen : oracle_comp exp_spec (α × γ))
(is_valid : α × γ → β × S → oracle_comp exp_spec bool)
(adv_so : α × γ → sim_oracle adv_spec exp_spec S)
(exp_so : sim_oracle exp_spec (uniform_selecting ++ ∅) S')

/-- View a soundness experiment as a security experiment with no hidden information
or adversary oracles. In this case we are merely testing that some property (almost) always holds.
This allows us to phrase e.g. the fact that messages can always be decrypted in Elgamal
as a security experiment where an adversary attempts to find a message that can't decrypt. -/
def soundness_experiment.to_sec_experiment {exp_spec : oracle_spec} {α β S : Type}
  (exp : soundness_experiment exp_spec α β S) :
  sec_experiment exp_spec exp_spec α β unit unit S :=
{ inp_gen := exp.inp_gen ×ₘ return (),
  is_valid := λ x y, exp.is_valid x.1 y.1,
  adv_so := λ _, idₛₒ,
  exp_so := exp.exp_so }

/-- Automatic coercion from soundness experiment to security experiment. -/
instance {exp_spec : oracle_spec} {α β S : Type} :
  has_coe (soundness_experiment exp_spec α β S)
    (sec_experiment exp_spec exp_spec α β unit unit S) :=
⟨λ exp, soundness_experiment.to_sec_experiment exp⟩

variables {α β γ : Type} {adv_spec exp_spec : oracle_spec} {S S' : Type}

namespace sec_adversary

section advantage

/-- `adv.advantage exp so` is the chance that `adv` succeeds in the experiment defined by `exp`
when simulated using `so`, assuming we start with the default state for `so`. -/
noncomputable def advantage (adv : sec_adversary adv_spec α β)
  (exp : sec_experiment adv_spec exp_spec α β γ S S') : ℝ≥0∞ :=
⁅= tt | dsimulate' exp.exp_so
  (do {x ← exp.inp_gen, z ← dsimulate (exp.adv_so x) (adv.run x.1), exp.is_valid x z})⁆

-- /-- version of `sec_adversary.advantage` where the initial input is fixed,
-- rather than being drawn from the input generator function. -/
-- noncomputable def sec_adversary.advantage_on_input (adv : sec_adversary adv_spec α β)
--   (exp : sec_experiment adv_spec exp_spec α β γ S)
--   (so : sim_oracle exp_spec uniform_selecting S') (x : α × γ) : ℝ≥0∞ :=
-- ⁅= tt | dsimulate' so
--   (do {z ← dsimulate (exp.so x) (adv.run x.1), exp.is_valid x z})⁆

end advantage

end sec_adversary

namespace sec_experiment

section always

/-- An experiment always succeeds if any possible adversary has an advantage of `1`. -/
def always_success (exp : sec_experiment adv_spec exp_spec α β γ S S') : Prop :=
∀ (adv : sec_adversary adv_spec α β), adv.advantage exp = 1

/-- An experiment always fails if any possible adversary has an advantage of `0`. -/
def always_failure (exp : sec_experiment adv_spec exp_spec α β γ S S') : Prop :=
∀ (adv : sec_adversary adv_spec α β), adv.advantage exp = 0

end always

end sec_experiment

/-- If two experiments `exp1` and `exp2` have the equivalent input generation function,
and for each possible input `adv2` performs better than `adv1` at succeeding in the experiment,
then `adv2` has a higher advantage than `adv1` in general.

TODO: for the forking lemma portion we need to allow a loss factor. -/
lemma advantage_le_advantage_of_inp_gen_eq {adv_spec exp_spec : oracle_spec} {α β γ S : Type}
  {adv_spec' exp_spec' : oracle_spec} {α β' γ S' : Type} {T T' : Type}
  (exp1 : sec_experiment adv_spec exp_spec α β γ S T)
  (exp2 : sec_experiment adv_spec' exp_spec' α β' γ S' T')
  (adv1 : sec_adversary adv_spec α β)
  (adv2 : sec_adversary adv_spec' α β')
  (h : dsimulate' exp1.exp_so exp1.inp_gen ≃ₚ
    dsimulate' exp2.exp_so exp2.inp_gen)
  (h' : ∀ x ∈ exp1.inp_gen.support,
    ⁅= tt | dsimulate' exp1.exp_so
        (do {z ← dsimulate (exp1.adv_so x) (adv1.run x.1), exp1.is_valid x z})⁆
      ≤ ⁅= tt | dsimulate' exp2.exp_so
          (do {z ← dsimulate (exp2.adv_so x) (adv2.run x.1), exp2.is_valid x z})⁆) :
  adv1.advantage exp1 ≤ adv2.advantage exp2 :=
begin
  sorry
end


section sec_reduction

structure sec_reduction {adv_spec exp_spec : oracle_spec} {α β γ S : Type}
  {adv_spec' exp_spec' : oracle_spec} {α' β' γ' S' : Type} {T T' : Type}
  (exp1 : sec_experiment adv_spec exp_spec α β γ S T)
  (exp2 : sec_experiment adv_spec' exp_spec' α' β' γ' S' T') :=
(loss_factor : ℝ≥0∞ → ℝ≥0∞)
(r : sec_adversary adv_spec α β → sec_adversary adv_spec' α' β')
(h : ∀ (adv : sec_adversary adv_spec α β),
  loss_factor (adv.advantage exp1) ≤ (r adv).advantage exp2)

end sec_reduction

-- section base

-- @[inline, reducible] def base_sec_experiment (exp_spec : oracle_spec) (α β : Type) :=
-- sec_experiment exp_spec exp_spec α β unit unit unit

-- def base_sec_experiment_of_is_valid {exp_spec : oracle_spec} {α β : Type}
--   (inp_gen : oracle_comp exp_spec α)
--   (is_valid : α → β → oracle_comp exp_spec bool)
--   (exp_so : sim_oracle exp_spec uniform_selecting unit) :
--   base_sec_experiment exp_spec α β :=
-- { inp_gen := (λ x, (x, ())) <$> inp_gen,
--   adv_so := λ _, idₛₒ,
--   is_valid := λ x y, is_valid x.1 y.1,
--   exp_so := exp_so}

-- -- /-- Version of `sec_adversary.advantage` when there is no "hidden" information or simulation state,
-- -- and where both the experiment and adversary use a common set of oracles. -/
-- -- noncomputable def sec_adversary.base_advantage (adv : sec_adversary adv_spec α β)
-- --   (exp : base_sec_experiment adv_spec α β) : ℝ≥0∞ :=
-- -- adv.advantage exp uniformₛₒ

-- -- lemma base_advantage_eq_prob_output (adv : sec_adversary adv_spec α β)
-- --   (exp : base_sec_experiment adv_spec α β) : adv.base_advantage exp =
-- --     ⁅= tt | do {x ← exp.inp_gen, z ← dsimulate (exp.so x) (adv.run x.1), exp.is_valid x z}⁆ :=
-- -- by rw [sec_adversary.base_advantage, sec_adversary.advantage,
-- --   uniform_oracle.prob_output_simulate']


-- end base

-- structure adversary_reduction (adv_spec₁ adv_spec₂ : oracle_spec) (α₁ β₁ α₂ β₂ : Type)
--   {exp_spec₁ exp_spec₂ : oracle_spec} {γ₁ γ₂ S₁ S₂} :=
-- (reduction : sec_adversary adv_spec₁ α₁ β₁ → sec_adversary adv_spec₂ α₂ β₂)

-- section soundness

/-- A `public_experiment` is a specific `sec_experiment` in which there isn't secret information
unavailable to the adversary during simulation (in the sense that this information is only
shared between the input generation function and the validation function). -/
def public_experiment {adv_spec exp_spec : oracle_spec} {α β S S' : Type}
  (inp_gen : oracle_comp exp_spec α)
  (adv_so : α → sim_oracle adv_spec exp_spec S)
  (is_valid : α → β → oracle_comp exp_spec bool)
  (exp_so : sim_oracle exp_spec (uniform_selecting ++ ∅) S') :
  sec_experiment adv_spec exp_spec α β unit S S' :=
{ inp_gen := (λ x, (x, ())) <$> inp_gen,
  is_valid := λ x y, is_valid x.1 y.1,
  adv_so := λ x, adv_so x.1,
  exp_so := exp_so }

-- end soundness

end oracle_comp
