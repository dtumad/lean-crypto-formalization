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

TODO: It would be good to get more done on improving the runtime, especially with simp versions.
Currently the number of lemmas tagged with `simp_dist_equiv` is limited by the runtime increase,
another alternative would be to increase the number of tags.
-/

open interactive interactive.types

namespace oracle_comp

/-- Structure to represent distributional equivalence rules.
TODO: this could be used to add features such as reverse rewriting -/
private meta structure d_eq_t :=
(d_eq : pexpr) (exact_eq : bool) (symm : bool)

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
private meta def apply_dist_equiv (d_eq : d_eq_t) : tactic unit :=
tactic.intros >> tactic.to_expr d_eq.d_eq >>= tactic.apply >> return ()

/-- Try to apply the given expresion to rewrite the left hand side of an equivalence. -/
private meta def apply_dist_equiv_trans (d_eq : d_eq_t) : tactic unit :=
do tactic.intros >> tactic.refine ``(dist_equiv.trans _ _),
  (list.length <$> tactic.get_goals) >>= rotate_to_dist_equiv,
  tactic.to_expr d_eq.d_eq >>= tactic.apply >> return ()

/-- Try to apply the given expresion to rewrite the left hand side of an equivalence. -/
private meta def apply_dist_eq_trans (d_eq : pexpr) : tactic unit :=
do tactic.intros >> tactic.refine ``(dist_equiv.trans (dist_equiv_of_eq _) _),
  (list.length <$> tactic.get_goals) >>= rotate_to_dist_equiv,
  tactic.to_expr d_eq >>= tactic.apply >> return ()

/-- Try to apply the passed in equivalence somewhere within the computation,
stopping after applying it once withen the computation.
If `fail_on_miss` is true it will throw an error if it doesn't make a rewrite.
The additional boolean argument is whether it should also be applied symmetrically.
Returns whether a `bool` representing if it made a rewrite somewhere. -/
private meta def traverse_dist_equiv (d_eq : d_eq_t) : bool → bool → tactic bool :=
λ fail_on_miss check_symm,
  -- Try to solve the goal by applying the given expression directly.
  apply_dist_equiv_trans d_eq >> return tt <|>
  -- Try to solve the goal by applying the given expression directly.
  -- apply_dist_eq_trans d_eq >> return tt <|>
  -- Try to apply the expression to the left portion of the bind.
  do {tactic.refine ``(dist_equiv.trans (oracle_comp.bind_dist_equiv_bind_of_dist_equiv_left _ _)
    _), (list.length <$> tactic.get_goals) >>= rotate_to_dist_equiv,
    (traverse_dist_equiv tt tt), (tactic.try tactic.reflexivity), return tt} <|>
  -- Try to apply the expression to the right portion of the bind.
  do {tactic.refine ``(dist_equiv.trans (oracle_comp.bind_dist_equiv_bind_of_dist_equiv_right' _ _
    _ _) _), (list.length <$> tactic.get_goals) >>= rotate_to_dist_equiv, tactic.intros,
    (traverse_dist_equiv tt tt), (tactic.try tactic.reflexivity), return tt} <|>
  -- Try to apply things on the other side of the equivalence
  (if check_symm = ff then tactic.fail () else
    tactic.refine ``(symm _) >> traverse_dist_equiv tt ff
      >> tactic.refine ``(symm _) >> return tt) <|>
  -- Fail if none of the previous attempts worked
  if fail_on_miss = ff then return ff else
    tactic.fail ("Failed to apply equivalence: " ++ (to_string d_eq.d_eq))

private meta def rec_rw_eqs (d_eq : d_eq_t) (fail_on_miss : bool) : ℕ → tactic unit
| 0 := return ()
| (n + 1) := do {b ← traverse_dist_equiv d_eq fail_on_miss tt,
    if b = tt then rec_rw_eqs n <|> return () else return ()}

/-- Loop through all the passed in equivalences, trying to apply them in order. -/
private meta def apply_dist_equiv_list (fail_on_miss : bool) (iters : ℕ) : list pexpr → tactic unit
| [] := tactic.reflexivity <|> return () -- Try to clear the final state with reflexive equality.
| (d :: d_eqs) := return (d_eq_t.mk d ff ff) >>= λ d_eq,
  (apply_dist_equiv d_eq <|> (rec_rw_eqs d_eq fail_on_miss iters
    >> apply_dist_equiv_list d_eqs))

/-- Tactic for reducing proofs of distributional equivalences between bind operations.
This introduces goals for pairwise proofs of equivalences between each component.
Attempts to discharge trivial goals using both `refl` and the given equivalences.
Supports `dist_equiv`, `eval_dist`, `prob_event`, `support`, and `fin_support`,
in each case trying to prove the goal by first proving a distributional equivalence. -/
@[interactive] meta def rw_dist_equiv
  (opt_d_eqs : parse (optional (pexpr_list))) :=
do passed_d_eqs ← return (opt_d_eqs.get_or_else []),
  by_dist_equiv, apply_dist_equiv_list tt 1 passed_d_eqs,
  tactic.try tactic.reflexivity,
  tactic.try by_dist_equiv

/-- Version of `rw_dist_equiv` that applies lemmas multiple times until it can't anymore.
The `opt_iters` param gives the maximum rewrites to make before stopping. -/
@[interactive] meta def simp_rw_dist_equiv
  (opt_d_eqs : parse (optional (pexpr_list)))
  (opt_iters : parse (optional lean.parser.small_nat)) :=
do passed_d_eqs ← return (opt_d_eqs.get_or_else []),
  iters ← return (opt_iters.get_or_else 6),
  by_dist_equiv, apply_dist_equiv_list tt iters passed_d_eqs,
  tactic.try tactic.reflexivity,
  tactic.try by_dist_equiv

/-- Version of `simp_rw_dist_equiv` that allows for a given equivalence to be used zero times,
and includes all external lemmas in the scope that are tagged with `simp_dist_equiv`-/
@[interactive] meta def simp_dist_equiv (no_tagged : parse only_flag)
  (opt_d_eqs : parse (optional (pexpr_list)))
  (opt_iters : parse (optional lean.parser.small_nat)) :=
do passed_d_eqs ← return (opt_d_eqs.get_or_else []),
  tagged_d_eqs ← if no_tagged then return [] else get_simp_dist_equiv_lemmas,
  iters ← return (opt_iters.get_or_else 6),
  by_dist_equiv, apply_dist_equiv_list ff iters (passed_d_eqs ++ tagged_d_eqs),
  apply_dist_equiv_list ff iters (passed_d_eqs ++ tagged_d_eqs).reverse, -- hack for ordering
  tactic.try tactic.reflexivity,
  tactic.try by_dist_equiv


end oracle_comp

section tests

variables {α β γ δ : Type} {spec spec' spec'' : oracle_spec}

section rw_dist_equiv

/-- `rw_dist_equiv` should be able to solve a reflexive distributional equivalence. -/
example (oa oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (oa >>= ob) ≃ₚ (oa >>= ob) :=
by rw_dist_equiv []

/-- `rw_dist_equiv` should be able to solve a goal that exactly matches an argument. -/
example (oa oa' : oracle_comp spec α) (hoa : oa ≃ₚ oa') : oa ≃ₚ oa' :=
by rw_dist_equiv [hoa]

/-- `rw_dist_equiv` should be able to solve a goal with differeing `oracle_spec`. -/
example (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) (hoa : oa ≃ₚ oa') : oa ≃ₚ oa' :=
by rw_dist_equiv [hoa]

/-- `rw_dist_equiv` should be able to solve an equivalence between bind operations. -/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (hoa : oa ≃ₚ oa') (hob : ∀ x, ob x ≃ₚ ob' x) : oa >>= ob ≃ₚ oa' >>= ob' :=
by rw_dist_equiv [hoa, hob]

-- /-- `rw_dist_equiv` should be able to work with e -/
-- example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
--   (hoa : oa = oa') (hob : ∀ x, ob x = ob' x) : oa >>= ob ≃ₚ oa' >>= ob' :=
-- by rw [hoa, hob]

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

/-- `rw_dist_equiv` should work on both sides of an equivalence -/
example (a : α) (ob : α → oracle_comp spec β) : ob a ≃ₚ return a >>= ob :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv]

example (a : α) (b : β) (oc : α → β → oracle_comp spec γ) :
  (return a >>= (λ x, return b >>= λ y, oc x y)) ≃ₚ oc a b :=
by simp_rw_dist_equiv [oracle_comp.return_bind_dist_equiv]


example (oa : oracle_comp spec α) (b : β) (oc : α → β → oracle_comp spec γ) :
  do {x ← oa, y ← return b, oc x y} ≃ₚ do {x ← oa, oc x b} :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv]

example (oa : oracle_comp spec α) (b : β) (oc : α → β → oracle_comp spec γ) :
  do {x ← oa, y ← return b, oc x y} ≃ₚ do {y ← return b, x ← oa, oc x b} :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv, oracle_comp.return_bind_dist_equiv]

example (oa : oracle_comp spec α) : do {x ← oa, n ← return 0, m ← return (n + 1), oa} ≃ₚ oa :=
by rw_dist_equiv [oracle_comp.return_bind_dist_equiv,
  oracle_comp.return_bind_dist_equiv, oracle_comp.bind_const_dist_equiv]

example (oa oa₀ : oracle_comp spec α) : do {oa₀, x ← oa, return x} ≃ₚ oa₀ >> oa :=
by rw_dist_equiv [oracle_comp.bind_return_dist_equiv]

end rw_dist_equiv

section simp_dist_equiv

/-- `simp_rw_dist_equiv` should be able to apply an equivalence multiple times. -/
example (oa oa' : oracle_comp spec α) (hoa : oa ≃ₚ oa') : oa >> oa ≃ₚ oa' >> oa' :=
by simp_rw_dist_equiv [hoa]

/-- `simp_dist_equiv` should be able to limit the set of equivalences. -/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : oracle_comp spec γ) (hoa : oa ≃ₚ oa') (hob : ∀ x, ob x ≃ₚ ob' x) :
  oc >> oa >>= ob ≃ₚ oc' >> oa' >>= ob' :=
by simp_dist_equiv only [hoa, hob, oracle_comp.bind_const_dist_equiv]

/-- `simp_dist_equiv` should work with tagged equivalences. -/
example (a : α) (ob : α → oracle_comp spec β) : return a >>= ob ≃ₚ ob a :=
by simp_dist_equiv

/-- `simp_dist_equiv` should be able to combine tagged and passed equivalences. -/
example (oa oa' oa'' : oracle_comp spec ℕ) (h : oa' ≃ₚ oa'') :
  do {n ← oa, z ← return 0, m ← oa', return (n + m)} ≃ₚ
    do {n ← (return 0 >> oa), m ← (return 0 >> oa''),  return (n + m)} :=
by simp_dist_equiv [h]

variables (oa oa' oa'' oa₀ : oracle_comp spec α)

end simp_dist_equiv

end tests