/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.instances
import computational_monads.oracle_algorithm
import computational_monads.asymptotics.polynomial_queries
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable

/-!
# Adversary for Security Games
-/

open_locale ennreal
open oracle_spec oracle_comp

/-- A security adversary `sec_adv adv_spec α β` is a computation taking inputs of type `α`
and computing a result of type `β` using oracles specified by `adv_spec`. -/
structure sec_adv (adv_spec : oracle_spec) (α β : Type) :=
(run : α → oracle_comp adv_spec β)
(run_qb : query_count adv_spec)

structure sec_exp (exp_spec : oracle_spec) (α β : Type)
  extends oracle_algorithm exp_spec :=
(inp_gen : oracle_comp exp_spec α)
(main : α → oracle_comp exp_spec β)
(is_valid : α → β → Prop)

namespace sec_exp

variables {exp_spec : oracle_spec} {α β γ : Type}

def run (exp : sec_exp exp_spec α β) :
  oracle_comp unif_spec (α × β) :=
exp.exec (do {x ← exp.inp_gen, y ← exp.main x, return (x, y)})

lemma run_def (exp : sec_exp exp_spec α β) :
  exp.run = exp.exec (do {x ← exp.inp_gen, y ← exp.main x, return (x, y)}) := rfl

-- lemma run_eq_simulate' (exp : sec_exp exp_spec α β) :
--   exp.run = simulate' exp.base_oracle
--     (do {x ← exp.inp_gen, y ← exp.main x, return (x, y)}) exp.init_state := rfl

noncomputable def advantage (exp : sec_exp exp_spec α β) : ℝ≥0∞ :=
⁅λ z, exp.is_valid z.1 z.2 | exp.run⁆

lemma advantage_eq_prob_event (exp : sec_exp exp_spec α β) :
  exp.advantage = ⁅λ z, exp.is_valid z.1 z.2 | exp.run⁆ := rfl

-- lemma le_advantage_of_forall_inp (exp : sec_exp exp_spec α β) (r : ℝ≥0∞)
--   (h : ∀ x ∈ (exp.exec exp.inp_gen).support,
--     r ≤ ⁅λ y, exp.is_valid x y | exp.exec (exp.main x)⁆) :
--   r ≤ exp.advantage :=
-- begin
--   rw [advantage, run, oracle_algorithm.exec_bind],
--   refine trans _ (prob_event_bind_mono_right _),
-- end

end sec_exp