/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_comp

/-!
# Induction Tactics for `oracle_comp`

This file defines a number of custom tactics that can be used in proofs involving `oracle_comp`s.
The definitions don't necessarilly reduce proof burden, but often simplify the statements,
in particular by giving more readable or simplified set of goals than regular `induction` tactics.
-/

open interactive (parse)
open lean.parser (ident)

namespace oracle_comp

variables {α β γ : Type} {spec : oracle_spec}

/-- Perform induction on the given computation, using `oracle_comp.induction_on` as the eliminator.
This has better naming conventions, and uses `return` and `>>=` over `pure'` and `bind'`. -/
meta def oracle_comp.default_induction (h : parse ident) :
  tactic (list (name × list expr × list (name × expr))) :=
do { oa ← tactic.get_local h,
  tactic.induction oa [`α, `a, `α, `β, `oa, `ob, `hoa, `hob, `i, `t] `oracle_comp.induction_on }

end oracle_comp