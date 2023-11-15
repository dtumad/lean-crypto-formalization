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

structure sec_experiment (exp_spec : oracle_spec) (α β : Type)
  extends oracle_algorithm exp_spec :=
(inp_gen : oracle_comp exp_spec α)
(main : α → oracle_comp exp_spec β)
(is_valid : α × β → Prop)

namespace sec_experiment

variables {exp_spec : oracle_spec} {α β γ : Type}

noncomputable def run_experiment (exp : sec_experiment exp_spec α β) :
  oracle_comp uniform_selecting (α × β) :=
exp.exec (do {x ← exp.inp_gen, y ← exp.main x, return (x, y)} )

noncomputable def advantage (exp : sec_experiment exp_spec α β) : ℝ≥0∞ :=
⁅exp.is_valid | exp.run_experiment⁆

end sec_experiment