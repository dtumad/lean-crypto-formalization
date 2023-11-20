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
open oracle_spec

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
  oracle_comp uniform_selecting (α × β) :=
exp.exec (do {x ← exp.inp_gen, y ← exp.main x, return (x, y)} )

noncomputable def advantage (exp : sec_exp exp_spec α β) : ℝ≥0∞ :=
⁅λ z, exp.is_valid z.1 z.2 | exp.run⁆

end sec_exp