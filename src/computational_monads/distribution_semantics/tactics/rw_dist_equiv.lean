/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad

/-!
# Tactic for Rewriting Terms by Distributional Equivalences

This file defines a tactic `rw_dist_equiv` that allows for rewriting terms by a distributional
equivalence `oa ≃ₚ oa'`, assuming the term is itself a distributional equivalence.
Generally this behaves like the `rewrite` tactic but for `≃ₚ` instead of `=`.
This is useful when you don't want to seperate terms like `⁅oa >>= ob⁆` into `⁅oa⁆ >>= ⁅ob⁆` first.
-/

open interactive interactive.types

variables {α β γ : Type} {spec : oracle_spec}

namespace oracle_comp

/-- Discharge a distributional equivalence between definitionally equal computations.-/
private meta def refl_dist_equiv_base : tactic unit :=
do `(%%oa ≃ₚ %%oa') ← tactic.target, (tactic.unify oa oa' >> tactic.reflexivity)

/-- Check that an expression is a proof of the form `∀ x₁, ... ∀ xₙ, oa ≃ₚ oa'`. -/
private meta def is_dist_equiv : expr → tactic bool
| `(%%oa ≃ₚ %%oa') := return tt
| `(∀ x, %%e) := is_dist_equiv e
| _ := return ff

/-- Rotate the goals until the current goal is a distributional equivalence.
Used to move to the main goal after applying a lemma with extra metavariables. -/
private meta def rotate_to_dist_equiv : ℕ → tactic bool
| 0 := return ff
| (n + 1) := do b ← tactic.target >>= is_dist_equiv,
    if b = tt then return tt else tactic.rotate 1 >> rotate_to_dist_equiv n

/-- Try to apply the given expression to solve the goal, returning whether it succeeds or not. -/
private meta def apply_dist_equiv (d_eq : pexpr) : tactic unit :=
tactic.to_expr d_eq >>= tactic.apply >> return ()

/-- Try to apply the given expresion to rewrite the left hand side of an equivalence. -/
private meta def apply_dist_equiv_trans (d_eq : pexpr) : tactic unit :=
do tactic.intros >>
  tactic.refine ``(trans _ _), (list.length <$> tactic.get_goals) >>= rotate_to_dist_equiv,
  tactic.to_expr d_eq >>= tactic.apply >> return ()

/-- Try to apply the passed in equivalence somewhere within the computation,
stopping after applying it once withen the computation.
Returns `tt` iff the entire original goal has been solved. -/
private meta def traverse_dist_equiv (d_eq : pexpr) : expr → tactic unit
| `(%%oa >>= %%ob ≃ₚ %%oc) := do {
  -- Try to solve the goal by applying the given expression directly.
  apply_dist_equiv d_eq <|>
  apply_dist_equiv_trans d_eq <|>
  -- Try to apply the expression to the left portion of the bind.
  do { tactic.refine ``(trans (oracle_comp.bind_dist_equiv_bind_of_dist_equiv_left _ _ _ _) _),
    (list.length <$> tactic.get_goals) >>= rotate_to_dist_equiv,
    (tactic.target >>= traverse_dist_equiv),
    (refl_dist_equiv_base <|> return ()) } <|>
  -- Try to apply the expression to the right portion of the bind.
  do { tactic.refine ``(trans (oracle_comp.bind_dist_equiv_bind_of_dist_equiv_right' _ _ _ _) _),
    (list.length <$> tactic.get_goals) >>= rotate_to_dist_equiv,
    (tactic.target >>= traverse_dist_equiv),
    (refl_dist_equiv_base <|> return ()) }
}
| _ := apply_dist_equiv d_eq <|> apply_dist_equiv_trans d_eq

/-- Loop through all the passed in equivalences, trying to apply them in order. -/
private meta def rewrite_dist_equivs (g : expr) : list pexpr → tactic unit
| [] := refl_dist_equiv_base <|> return () -- Try to clear the final state with reflexive equality.
| (d_eq :: d_eqs) := (tactic.target >>= traverse_dist_equiv d_eq
    <|> tactic.fail ("Failed to apply equivalence: " ++ (to_string d_eq)))
      >> rewrite_dist_equivs d_eqs -- If the application doesn't fail then keep applying.

/-- Tactic for reducing proofs of distributional equivalences between bind operations.
This introduces goals for pairwise proofs of equivalences between each component.
Attempts to discharge trivial goals using both `refl` and the given equivalences.
Supports `dist_equiv`, `eval_dist`, `prob_event`, `support`, and `fin_support`,
in each case trying to prove the goal by first proving a distributional equivalence. -/
@[interactive] meta def rw_dist_equiv (opt_d_eqs : parse (optional (pexpr_list))) : tactic unit :=
do g ← tactic.target, passed_d_eqs ← return (opt_d_eqs.get_or_else []),
match g with
-- If the target is a distributional equivalence, begin solving it immedeately.
| `(%%oa ≃ₚ %%oa') := rewrite_dist_equivs g passed_d_eqs >>
    tactic.try refl_dist_equiv_base
-- Fail if the goal isn't equality between distributional values.
| _ := tactic.fail "Goal must be an equality be a distributional equivalence."
end

end oracle_comp

section tests

/-- `rw_dist_equiv` should be able to solve a reflexive distributional equivalence. -/
example (oa oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (oa >>= ob) ≃ₚ (oa >>= ob) :=
by rw_dist_equiv []

/-- `rw_dist_equiv` should be able to solve a goal that exactly matches an argument. -/
example (oa oa' : oracle_comp spec α) (hoa : oa ≃ₚ oa') : oa ≃ₚ oa' :=
by rw_dist_equiv [hoa]

/-- `rw_dist_equiv` should be able to solve an equivalence between bind operations. -/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (hoa : oa ≃ₚ oa') (hob : ∀ x, ob x ≃ₚ ob' x) : oa >>= ob ≃ₚ oa' >>= ob' :=
by rw_dist_equiv [hoa, hob]

/-- `rw_dist_equiv` should be able to solve an equivalence between bind operations. -/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (hoa : oa ≃ₚ oa') (hob : ∀ x, ob x ≃ₚ ob' x) : oa >>= ob ≃ₚ oa' >>= ob' :=
by rw_dist_equiv [hob, hoa] -- different ordering

/-- `rw_dist_equiv` should be able to solve an equvialence between nested bind operations -/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : β → oracle_comp spec γ) (hoa : oa ≃ₚ oa') (hob : ∀ x, ob x ≃ₚ ob' x)
  (hoc : ∀ y, oc y ≃ₚ oc' y) : oa >>= ob >>= oc ≃ₚ oa' >>= ob' >>= oc' :=
by rw_dist_equiv [hoc, hoa, hob]

/-- `rw_dist_equiv` should be able to solve an equvialence between nested bind operations -/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : β → oracle_comp spec γ) (hoa : oa ≃ₚ oa') (hob : ∀ x, ob x ≃ₚ ob' x)
  (hoc : ∀ y, oc y ≃ₚ oc' y) : oa >>= ob >>= oc ≃ₚ oa' >>= ob' >>= oc' :=
by rw_dist_equiv [hoa, hob, hoc]

/-- `rw_dist_equiv` should work with externally defined lemmas. -/
example (a : α) (ob : α → oracle_comp spec β) : return a >>= ob ≃ₚ ob a :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv]

example (a : α) (b : β) (oc : α → β → oracle_comp spec γ) :
  (return a >>= (λ x, return b >>= λ y, oc x y)) ≃ₚ oc a b :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv,
  oracle_comp.return_bind_dist_equiv]

example (oa : oracle_comp spec α) (b : β) (oc : α → β → oracle_comp spec γ) :
  do {x ← oa, y ← return b, oc x y} ≃ₚ do {x ← oa, oc x b} :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv]

example (oa : oracle_comp spec α) : do {x ← oa, n ← return 0, m ← return (n + 1), oa} ≃ₚ oa :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv,
  oracle_comp.return_bind_dist_equiv, oracle_comp.bind_const_dist_equiv]

end tests