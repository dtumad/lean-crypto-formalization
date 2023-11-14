/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.by_dist_equiv

/-!
# Induction Tactic for Splitting an Equivalence into Line by Line Equivalences

This file defines a tactic `pairwise_dist_equiv` for working with and proving instances of
`dist_equiv` between sequenced computations, by splitting the goal into line-by-line equivalences.

TODO: Pass in custom names for new variables
-/

open interactive interactive.types

variables {α β γ : Type} {spec : oracle_spec}

namespace oracle_comp

private meta def intro_base : option (list name) → tactic (option (list name))
| none := tactic.intros >> return none
| (some []) := tactic.intros >> return none
| (some (n :: ns)) := (tactic.intro n >> intro_base ns) <|> return (some (n :: ns))

/-- Discharge a distributional equivalence between definitionally equal computations.-/
private meta def refl_dist_equiv_base : tactic unit :=
do `(%%oa ≃ₚ %%oa') ← tactic.target, (tactic.unify oa oa' >> tactic.reflexivity)

/-- Attempt to discharge the current goal using the given lemma (potentially in reverse).
Returns a boolean representing whether or not more lemmas should be applied -/
private meta def rw_dist_equiv_base (d_eq : expr) : tactic bool :=
(tactic.apply d_eq >> return ff) <|>
  (tactic.refine ``(symm _) >> tactic.apply d_eq >> return ff) <|> return tt

/-- Given a list of distributional equivalences, call `rw_dist_equiv_base` until one succeeds.
Immediately stops if the current goal is discharged. -/
private meta def apply_dist_equivs : list pexpr → tactic unit
| [] := tactic.rotate 1 -- If the goal is never solved then rotate it to the last goal.
| (d_eq :: d_eqs) := (tactic.to_expr d_eq >>= rw_dist_equiv_base >>=
    λ b, if b = tt then apply_dist_equivs d_eqs else return ())

private meta def try_solve (d_eq : list pexpr) : tactic unit :=
refl_dist_equiv_base <|> apply_dist_equivs d_eq

private meta def is_shallow_equiv : expr → bool
| `(%%oa >>= %%ob ≃ₚ %%oa' >>= %%ob') := tt
| `(%%f <$> %%oa ≃ₚ %%f' <$> %%oa') := tt
| _ := ff

/-- Destruct a distributional equivalence by recursively splitting equivalences between binds
into multiple equivalences between their individual components.
For other equivalences will defer to `pairwise_dist_equiv_base`. -/
private meta def destruct_pairwise_dist_equiv (d_eq : list pexpr) (deep : bool)
  : option (list name) → ℕ → expr → tactic (option (list name))
| opt_names (n + 1) e := if is_shallow_equiv e ∨ deep = tt then do {
  -- Split the goal into two seperate distributional equivalences.
  tactic.refine ``(oracle_comp.bind_dist_equiv_bind_of_dist_equiv _ _),
  -- Attempt to recursively solve the first equivalence.
  opt_names' ← tactic.target >>= destruct_pairwise_dist_equiv opt_names n,
  -- Introduce any new variables for the second equivalence.
  opt_names'' ← intro_base opt_names',
  -- Attempt to recursively solve the second equivalence
  tactic.target >>= destruct_pairwise_dist_equiv opt_names'' n
} <|> try_solve d_eq >> return opt_names else try_solve d_eq >> return opt_names
| opt_names 0 _ := try_solve d_eq >> return opt_names

meta def deep_flag : lean.parser bool := (lean.parser.tk "deep" *> return tt) <|> return ff

/-- Tactic for reducing proofs of distributional equivalences between bind operations.
This introduces goals for pairwise proofs of equivalences between each component.
Attempts to discharge trivial goals using both `refl` and the given equivalences.
Supports `dist_equiv`, `eval_dist`, `prob_event`, `support`, and `fin_support`,
in each case trying to prove the goal by first proving a distributional equivalence.
If `deep` is true then it will attempt to break things pairwise eagerly,
even when the peices don't look like an equivalence between binds syntactically. -/
private meta def pairwise_dist_equiv_aux (deep : bool)
  (opt_d_eqs : option (list pexpr)) (opt_depth : option ℕ)
  (opt_names : option (list name)) : tactic unit :=
do g ← tactic.target,
  passed_d_eqs ← return (opt_d_eqs.get_or_else []),
  passed_depth ← return (opt_depth.get_or_else 100),
  tagged_d_eqs ← get_simp_dist_equiv_lemmas,
  tagged_d_eqs' ← get_pairwise_dist_equiv_lemmas,
  d_eqs ← return (passed_d_eqs ++ tagged_d_eqs ++ tagged_d_eqs'),
  by_dist_equiv,
  tactic.target >>= destruct_pairwise_dist_equiv d_eqs deep opt_names passed_depth >> return ()

@[interactive] meta def pairwise_dist_equiv (opt_d_eqs : parse (optional (pexpr_list)))
  (opt_depth : parse (optional (lean.parser.small_nat)))
  (opt_names : parse (optional (with_ident_list))) : tactic unit :=
do pairwise_dist_equiv_aux ff opt_d_eqs opt_depth opt_names

@[interactive] meta def pairwise_dist_equiv_deep (opt_d_eqs : parse (optional (pexpr_list)))
  (opt_depth : parse (optional (lean.parser.small_nat)))
  (opt_names : parse (optional (with_ident_list))): tactic unit :=
do pairwise_dist_equiv_aux tt opt_d_eqs opt_depth opt_names

end oracle_comp

section tests

/-- `pairwise_dist_equiv` should be able to split the components of the bind,
and automatically discharge goals that have provided equivalences or definitional equality. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
by pairwise_dist_equiv [h]

example (oa oa' : oracle_comp spec α) (f : α → β) (h : oa ≃ₚ oa') : f <$> oa ≃ₚ f <$> oa' :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should work on `eval_dist`. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : ⁅oa >>= ob⁆ = ⁅oa' >>= ob⁆ :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should work on `prob_output`. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β) (y y' : β) (h' : oa ≃ₚ oa') :
  ⁅= y | oa >>= ob⁆ = ⁅= y | oa' >>= ob⁆ :=
by pairwise_dist_equiv [h']

/-- `pairwise_dist_equiv` should work on `prob_event`. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β) (e : set β) (h' : oa ≃ₚ oa') :
  ⁅e | oa >>= ob⁆ = ⁅e | oa' >>= ob⁆ :=
by pairwise_dist_equiv [h']

/-- `pairwise_dist_equiv` should work on `support`. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob).support = (oa' >>= ob).support :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should work on `fin_support`. -/
example [decidable_eq β] (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob).fin_support = (oa' >>= ob).fin_support :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should be able to apply given equivalences in reverse as well. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa' >>= ob) ≃ₚ (oa >>= ob) :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should leave extra goals for equivalences it can't solve-/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (f : α → oracle_comp spec α) (oc oc' : α → β → oracle_comp spec γ)
  (h : oa ≃ₚ oa') (h' : ∀ a, ob a ≃ₚ ob' a) (h'' : ∀ a b, oc a b ≃ₚ oc' a b) :
  ((oa >>= f) >>= λ x, ob x >>= λ y, oc x y) ≃ₚ ((oa' >>= f) >>= λ x, ob' x >>= λ y, oc' x y) :=
begin
  pairwise_dist_equiv [],
  apply h, apply h', apply h'',
end

/-- `pairwise_dist_equiv` should break equivalences eagerly if the deep flag is set -/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') (h' : ∀ a, ob a ≃ₚ ob' a) : oa >>= ob ≃ₚ oa' >>= ob' :=
begin
  let oc := oa >>= ob,
  let oc' := oa' >>= ob',
  show oc ≃ₚ oc',
  pairwise_dist_equiv [h, h'], -- Shouldn't work without deep evaluation.
  pairwise_dist_equiv_deep [h, h'], -- Works with deep evaluation.
end


/-- If two bind operations have mismatched intermediate types, but there is an existing equivalence
between the two, then `pairwise_dist_equiv` should be able to solve without error. -/
example (oa : oracle_comp spec α) (oa' : oracle_comp spec γ)
  (ob : α → oracle_comp spec β) (ob' : γ → oracle_comp spec β)
  (h : oa >>= ob ≃ₚ oa' >>= ob') : oa >>= ob ≃ₚ oa' >>= ob' :=
by pairwise_dist_equiv [h]

example (oa oa' : oracle_comp spec α) (hoa : oa ≃ₚ oa')
  (ob ob' : α → oracle_comp spec β) (hob : ∀ a, ob a ≃ₚ ob' a)
  (oc oc' : β → oracle_comp spec γ) (hoc : ∀ b, oc b ≃ₚ oc' b) :
  oa >>= (λ x, ob x >>= oc) ≃ₚ oa' >>= (λ x, ob' x >>= oc') :=
by pairwise_dist_equiv [hoa, hob, hoc]

/-- `pairwise_dist_equiv` should be able to handle nested branching of binding operations,
as well as equivalence arguments with many parameters -/
example (oa oa' : oracle_comp spec α) (hoa : oa ≃ₚ oa')
  (ob ob' : α → oracle_comp spec β) (hob : ∀ a, ob a ≃ₚ ob' a)
  (oc oc' : α → β → oracle_comp spec α) (hoc : ∀ a b, oc a b ≃ₚ oc' a b) :
  ((oa' >>= λ x, ob x >>= λ y, oc x y) >>= λ x, ob x >>= λ y, oc' x y) ≃ₚ
    ((oa >>= λ x, ob' x >>= λ y, oc' x y) >>= λ x, ob' x >>= λ y, oc' x y) :=
by pairwise_dist_equiv [hoa, hob, hoc]

/-- `pairwise_dist_equiv` accepts a depth argument. -/
example (oa oa' : oracle_comp spec α) (hoa : oa ≃ₚ oa')
  (ob ob' : α → oracle_comp spec β) (hob : ∀ a, ob a ≃ₚ ob' a)
  (oc oc' : β → oracle_comp spec γ) (hoc : ∀ b, oc b ≃ₚ oc' b) :
  oa >>= (λ x, ob x >>= oc) ≃ₚ oa' >>= (λ x, ob' x >>= oc') :=
begin
  pairwise_dist_equiv 1,
  exact hoa,
  pairwise_dist_equiv 0,
  pairwise_dist_equiv [hob, hoc] 1,
end

/-- `pairwise_dist_equiv` can do non-syntactical equality checking. -/
example (oa oa' : ℕ → oracle_comp spec α) (h : ∀ n, oa n ≃ₚ oa' n):
  (do {x ← return 6, y ← oa x, return 5} : oracle_comp spec ℕ) ≃ₚ
  (do {x ← return (1 * 2 * 3), y ← oa' x, return (10 - 3 - 2)} : oracle_comp spec ℕ) :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` allows custom variable names -/
example (oa : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : β → oracle_comp spec γ) (h : ∀ x ∈ oa.support, ob x ≃ₚ ob' x)
  (h' : ∀ y ∈ (oa >>= ob).support, oc y ≃ₚ oc' y) : oa >>= ob >>= oc ≃ₚ oa >>= ob' >>= oc' :=
begin
  pairwise_dist_equiv with xx hxx yy hyy,
  exact h xx hxx,
  exact h' yy hyy,
end

end tests