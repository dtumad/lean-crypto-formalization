/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.return
import computational_monads.distribution_semantics.bind

/-!
# Tactic for Reducing a Goal to a Distributional Equivalence.

This file defines a tactic `by_dist_equiv` for turning a goal into one of the form `oa ≃ₚ oa'`.
This works assuming the goal is an equality between `support`, `fin_support`, `eval_dist`,
`prob_output`, or `prob_event`, by applying corresponding `dist_equiv` lemmas.
-/

open interactive interactive.types

variables {α β γ : Type} {spec : oracle_spec}

namespace oracle_comp

/-- Tactic for reducing proofs of distributional equivalences between bind operations.
This introduces goals for pairwise proofs of equivalences between each component.
Attempts to discharge trivial goals using both `refl` and the given equivalences.
Supports `dist_equiv`, `eval_dist`, `prob_event`, `support`, and `fin_support`,
in each case trying to prove the goal by first proving a distributional equivalence. -/
@[interactive] meta def by_dist_equiv : tactic unit :=
do g ← tactic.target,
match g with
| `(%%oa ≃ₚ %%oa') := return ()
| `(⁅%%oa⁆ = ⁅%%oa'⁆) := tactic.refine ``(oracle_comp.dist_equiv.def.1 _)
| `(⁅= %%x | %%oa⁆ = ⁅= %%x' | %%oa'⁆) :=
    tactic.refine ``(oracle_comp.dist_equiv.prob_output_eq _ _)
| `(⁅%%e | %%oa⁆ = ⁅%%e' | %%oa'⁆) :=
    tactic.unify e e' >> tactic.refine ``(oracle_comp.dist_equiv.prob_event_eq _ %%e)
| `(oracle_comp.support %%oa = oracle_comp.support %%oa') :=
    tactic.refine ``(oracle_comp.dist_equiv.support_eq _)
| `(oracle_comp.fin_support %%oa = oracle_comp.fin_support %%oa') :=
    tactic.refine ``(oracle_comp.dist_equiv.fin_support_eq _)
| _ := tactic.fail "Goal can't be directly reduced to a distributional equivalence."
end

end oracle_comp

section tests

variables (oa oa' : oracle_comp spec α)

example (hoa : oa ≃ₚ oa') : oa ≃ₚ oa' :=
by {by_dist_equiv, exact hoa}

example (hoa : oa ≃ₚ oa') : oa.support = oa'.support :=
by {by_dist_equiv, exact hoa}

example [decidable_eq α] (hoa : oa ≃ₚ oa') : oa.fin_support = oa'.fin_support :=
by {by_dist_equiv, exact hoa}

example (hoa : oa ≃ₚ oa') : ⁅oa⁆ = ⁅oa'⁆ :=
by {by_dist_equiv, exact hoa}

example (hoa : oa ≃ₚ oa') (x : α) : ⁅= x | oa⁆ = ⁅= x | oa'⁆ :=
by {by_dist_equiv, exact hoa}

example (hoa : oa ≃ₚ oa') (e : set α) : ⁅e | oa⁆ = ⁅e | oa'⁆ :=
by {by_dist_equiv, exact hoa}

end tests