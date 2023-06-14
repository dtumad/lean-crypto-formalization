/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.return
import computational_monads.distribution_semantics.bind

/-!
# Induction Tactics for Distribution Semantics of `oracle_comp`

This file defines custom tactics for working with and proving instances of `dist_equiv`.
-/

open interactive interactive.types

variables {α β γ : Type} {spec : oracle_spec}

/-- Tag for lemmas to be automatically applied by `pairwise_dist_equiv`. -/
meta def simp_dist_equiv : user_attribute :=
{ name := "simp_dist_equiv",
  descr := "Lemmas tagged with this attribute are automatically called by the
              `pairwise_dist_equiv` tactic, similar to the way the `simp` tactic works." }

run_cmd attribute.register "simp_dist_equiv"

private meta def get_simp_dist_equiv_lemmas : tactic (list pexpr) :=
do {tagged_d_eqs ← (attribute.get_instances "simp_dist_equiv"),
  t' ← mmap tactic.get_decl tagged_d_eqs,
  d ←  return (list.map declaration.value t'),
  q ← return (list.map pexpr.of_expr d),
  return q
}

namespace oracle_comp

/-- Discharge a distributional equivalence between definitionally equal computations.-/
private meta def refl_dist_equiv_base : tactic unit :=
do `(%%oa ≃ₚ %%oa') ← tactic.target, (tactic.unify oa oa' >> tactic.reflexivity)

/-- Attempt to discharge the current goal using the given lemma (potentially in reverse).
Returns a boolean representing success or failure -/
private meta def rw_dist_equiv_base (d_eq : expr) : tactic unit :=
(tactic.apply d_eq >> return ()) <|>
  (tactic.refine ``(symm _) >> tactic.apply d_eq >> return ())

/-- Given a list of distributional equivalences, call `rw_dist_equiv_base` until one succeeds.
Immediately stops if the current goal is discharged. -/
private meta def apply_dist_equivs : list pexpr → tactic unit
| [] := tactic.rotate 1 -- If the goal is never solved then rotate it to the last goal.
| (d_eq :: d_eqs) := tactic.to_expr d_eq >>= rw_dist_equiv_base <|>
                      apply_dist_equivs d_eqs

-- do
--     (d_eqs.mmap (λ d, tactic.to_expr d >>= rw_dist_equiv_base) >>=
--       λ bs, if tt ∉ bs then tactic.rotate 1 else return ()) -- Rotate if not discharged.

/-- Destruct a distributional equivalence by recursively splitting equivalences between binds
into multiple equivalences between their individual components.
For other equivalences will defer to `pairwise_dist_equiv_base`. -/
private meta def destruct_pairwise_dist_equiv (d_eq : list pexpr) : expr → tactic unit
| `(%%oa >>= %%ob ≃ₚ %%oa' >>= %%ob') := do {
  -- Check that the first components of each bind operation have the same type.
  `(oracle_comp %%spec %%α) ← tactic.infer_type oa,
  `(oracle_comp %%spec' %%α') ← tactic.infer_type oa',
  tactic.unify α α', -- Will exit to the `pairwise_dist_equiv_base` below on failure.
  -- Split the goal into two seperate distributional equivalences.
  tactic.refine ``(oracle_comp.bind_dist_equiv_bind_of_dist_equiv _ _),
  -- Attempt to recursively solve the first equivalence.
  tactic.target >>= destruct_pairwise_dist_equiv,
  -- Attempt to recursively solve the second equivalence
  tactic.intros >> tactic.target >>= destruct_pairwise_dist_equiv
  -- On failure, try to solve the equivalence without any recursion.
} <|> refl_dist_equiv_base <|> apply_dist_equivs d_eq
| `(%%f <$> %%oa ≃ₚ %%f' <$> %%oa') := do {
  -- Check that the first components of each bind operation have the same type.
  `(oracle_comp %%spec %%α) ← tactic.infer_type oa,
  `(oracle_comp %%spec' %%α') ← tactic.infer_type oa',
  tactic.unify α α', -- Will exit to the `pairwise_dist_equiv_base` below on failure.
  -- Split the goal into two seperate distributional equivalences.
  tactic.refine ``(oracle_comp.bind_dist_equiv_bind_of_dist_equiv _ _),
  -- Attempt to recursively solve the first equivalence.
  tactic.target >>= destruct_pairwise_dist_equiv,
  -- Attempt to recursively solve the second equivalence
  tactic.intros >> tactic.target >>= destruct_pairwise_dist_equiv
  -- On failure, try to solve the equivalence without any recursion.
} <|> refl_dist_equiv_base <|> apply_dist_equivs d_eq
| _ := refl_dist_equiv_base <|> apply_dist_equivs d_eq

/-- Tactic for reducing proofs of distributional equivalences between bind operations.
This introduces goals for pairwise proofs of equivalences between each component.
Attempts to discharge trivial goals using both `refl` and the given equivalences.
Supports `dist_equiv`, `eval_dist`, `prob_event`, `support`, and `fin_support`,
in each case trying to prove the goal by first proving a distributional equivalence. -/
@[interactive] meta def pairwise_dist_equiv (opt_d_eqs : parse (optional (pexpr_list))) :=
do g ← tactic.target,
  passed_d_eqs ← return (opt_d_eqs.get_or_else []),
  tagged_d_eqs ← get_simp_dist_equiv_lemmas,
  d_eqs ← return (passed_d_eqs ++ tagged_d_eqs),
match g with
-- If the target is a distributional equivalence, begin solving it immedeately.
| `(%%oa ≃ₚ %%oa') := destruct_pairwise_dist_equiv d_eqs g
-- If the target is an equality between `eval_dist`s, convert to equivalence notation first.
| `(⁅%%oa⁆ = ⁅%%oa'⁆) := tactic.refine ``(oracle_comp.dist_equiv.def.1 _) >>
    tactic.target >>= destruct_pairwise_dist_equiv d_eqs
-- If the target is an equality between `prob_event`s, switch to equivalence first
| `(⁅%%e | %%oa⁆ = ⁅%%e' | %%oa'⁆) :=
    tactic.unify e e' >> tactic.refine ``(oracle_comp.dist_equiv.prob_event_eq _ %%e) >>
      tactic.target >>= destruct_pairwise_dist_equiv d_eqs <|>
    tactic.refine ``(oracle_comp.dist_equiv.prob_event_eq_of_inter_support_eq _ _) >>
      tactic.target >>= destruct_pairwise_dist_equiv d_eqs
-- If the target is an equality between `support`s, switch to equivalence first
| `(oracle_comp.support %%oa = oracle_comp.support %%oa') :=
    tactic.refine ``(oracle_comp.dist_equiv.support_eq _) >>
      tactic.target >>= destruct_pairwise_dist_equiv d_eqs
-- If the target is an equality between `fin_support`s, switch to equivalence first
| `(oracle_comp.fin_support %%oa = oracle_comp.fin_support %%oa') :=
    tactic.refine ``(oracle_comp.dist_equiv.fin_support_eq _) >>
      tactic.target >>= destruct_pairwise_dist_equiv d_eqs
| _ := tactic.fail "Goal must be a distributional equivalence"
end

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

/-- `pairwise_dist_equiv` should work on `prob_event`. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β) (e e' : set β) (h' : oa ≃ₚ oa')
  (h : e ∩ (oa >>= ob).support = e' ∩ (oa >>= ob).support) : ⁅e | oa >>= ob⁆ = ⁅e' | oa' >>= ob⁆ :=
by {pairwise_dist_equiv [h'], exact h}

/-- `pairwise_dist_equiv` should work on `support`. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob).support = (oa' >>= ob).support :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should work on `fin_support`. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
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

/-- If two bind operations have mismatched intermediate types, but there is an existing equivalence
between the two, then `pairwise_dist_equiv` should be able to solve without error. -/
example (oa : oracle_comp spec α) (oa' : oracle_comp spec γ)
  (ob : α → oracle_comp spec β) (ob' : γ → oracle_comp spec β)
  (h : oa >>= ob ≃ₚ oa' >>= ob') : oa >>= ob ≃ₚ oa' >>= ob' :=
by pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should be able to handle nested branching of binding operations,
as well as equivalence arguments with many parameters -/
example (oa oa' : oracle_comp spec α) (hoa : oa ≃ₚ oa')
  (ob ob' : α → oracle_comp spec β) (hob : ∀ a, ob a ≃ₚ ob' a)
  (oc oc' : α → β → oracle_comp spec α) (hoc : ∀ a b, oc a b ≃ₚ oc' a b) :
  ((oa' >>= λ x, ob x >>= λ y, oc x y) >>= λ x, ob x >>= λ y, oc' x y) ≃ₚ
    ((oa >>= λ x, ob' x >>= λ y, oc' x y) >>= λ x, ob' x >>= λ y, oc' x y) :=
by pairwise_dist_equiv [hoa, hob, hoc]

/-- `pairwise_dist_equiv` can do non-syntactical equality checking. -/
example (oa oa' : ℕ → oracle_comp spec α) (h : ∀ n, oa n ≃ₚ oa' n):
  (do {x ← return 6, y ← oa x, return 5} : oracle_comp spec ℕ) ≃ₚ
  (do {x ← return (1 * 2 * 3), y ← oa' x, return (10 - 3 - 2)} : oracle_comp spec ℕ) :=
by pairwise_dist_equiv [h]

end tests