/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad

/-!
# Induction Tactics for Distribution Semantics of `oracle_comp`

This file defines custom tactics for working with `support`, `eval_dist`, and `prob_event`,
specifically focusing on using `dist_equiv` for rewriting expressions.
-/

open interactive interactive.types tactic

variables {α β γ : Type} {spec : oracle_spec}

namespace tactic.interactive.oracle_comp

meta def rw_dist_equiv_base (d_eq : expr) : tactic unit :=
tactic.apply d_eq >> return () <|>
  tactic.refine ``(symm _) >> tactic.apply d_eq >> return () <|>
    return ()

/-- Attempt to discharge a distributional equivalence between two computations by todo. -/
meta def pairwise_dist_equiv_base (d_eqs : list pexpr) : tactic unit :=
do `(%%oa ≃ₚ %%oa') ← tactic.target <|> tactic.fail ("Goal must be a distributional equivalence"),
  -- Immedeately discharge the goal if the equivalence is between equal objects
  (tactic.unify oa oa' >> tactic.congr) <|>
    (d_eqs.mmap (λ d, tactic.to_expr d >>= rw_dist_equiv_base) >> return ())

/-- Destruct a distributional equivalence by recursively splitting equivalences between binds
into multiple equivalences between their individual components.
For other equivalences will defer to `pairwise_dist_equiv_base`. -/
meta def destruct_pairwise_dist_equiv (d_eq : list pexpr) : expr → tactic unit
| `((%%oa >>= %%ob ≃ₚ %%oa' >>= %%ob')) := do {
  -- Check that the first components of each bind operation have the same type.
  `(oracle_comp %%spec %%α) ← tactic.infer_type oa,
  `(oracle_comp %%spec %%α') ← tactic.infer_type oa',
  tactic.unify α α', -- Will exit to the `pairwise_dist_equiv_base` below on failure.
  -- Split the goal into two seperate distributional equivalences.
  tactic.refine ``(oracle_comp.bind_dist_equiv_bind_of_dist_equiv _ _),
  -- Attempt to recursively solve the first equivalence.
  tactic.intros,
  tactic.target >>= destruct_pairwise_dist_equiv,
  -- Switch to the second equivalence and attempt to solve it.
  tactic.rotate 1,
  tactic.intros,
  tactic.target >>= destruct_pairwise_dist_equiv
  -- On failure, try to solve the equivalence without any recursion.
} <|> pairwise_dist_equiv_base d_eq
| _ := pairwise_dist_equiv_base d_eq

/-- Tactic for reducing proofs of distributional equivalences between bind operations
into pairwise proofs of equivalences between each component.
Attempts to discharge trivial goals using both `congr` and the given equivalences. -/
meta def pairwise_dist_equiv (opt_d_eqs : parse (optional (pexpr_list))) : tactic unit :=
tactic.target >>= destruct_pairwise_dist_equiv (opt_d_eqs.get_or_else [])

end tactic.interactive.oracle_comp

section examples

/-- `pairwise_dist_equiv` should be able to split the components of the bind,
and automatically discharge goals that have provided equivalences or definitional equality. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
by oracle_comp.pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should be able to apply given equivalences in reverse as well. -/
example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa' >>= ob) ≃ₚ (oa >>= ob) :=
by oracle_comp.pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should leave extra goals for equivalences it can't solve-/
example (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : α → β → oracle_comp spec γ) (h : oa ≃ₚ oa') (h' : ∀ a, ob a ≃ₚ ob' a)
  (h'' : ∀ a b, oc a b ≃ₚ oc' a b) :
  (oa >>= λ x, ob x >>= λ y, oc x y) ≃ₚ (oa' >>= λ x, ob' x >>= λ y, oc' x y) :=
by {oracle_comp.pairwise_dist_equiv, apply h'', apply h, apply h'}

/-- If two bind operations have mismatched intermediate types, but there is an existing equivalence
between the two, then `pairwise_dist_equiv` should be able to solve without error. -/
example (oa : oracle_comp spec α) (oa' : oracle_comp spec γ)
  (ob : α → oracle_comp spec β) (ob' : γ → oracle_comp spec β)
  (h : oa >>= ob ≃ₚ oa' >>= ob') :
  oa >>= ob ≃ₚ oa' >>= ob' :=
by oracle_comp.pairwise_dist_equiv [h]

/-- `pairwise_dist_equiv` should be able to handle nested branching of binding operations. -/
example (oa : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : α → β → oracle_comp spec α)
  (h : ∀ a, ob a ≃ₚ ob' a) (h' : ∀ a b, oc a b ≃ₚ oc' a b) :
  ((oa >>= λ x, ob x >>= λ y, oc x y) >>= λ x, ob x >>= λ y, oc x y) ≃ₚ
    ((oa >>= λ x, ob x >>= λ y, oc' x y) >>= λ x, ob' x >>= λ y, oc' x y) :=
by oracle_comp.pairwise_dist_equiv [h, h']

end examples