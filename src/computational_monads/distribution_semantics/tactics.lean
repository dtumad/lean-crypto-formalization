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

open interactive (parse loc.ns)
open lean.parser (ident)
open lean.parser (tk)
open tactic.interactive («have» «suffices»)
open interactive.types (texpr location)

variables {α β γ : Type} {spec : oracle_spec}


namespace tactic.interactive


-- /-- Using a given equivalence `d : oa ≃ₚ oa'`, check if the goal is an equality with
-- `oa.support` on either side, and if so replace it with `oa'.support`. -/
-- meta def rw_support_base_goal (d : parse texpr) : tactic unit :=
-- do {
--   d_eq ← tactic.i_to_expr d, -- Get the left and right sides of the distributional equivalence.
--   `(oracle_comp.dist_equiv %%oa_left %%oa_right) ← tactic.infer_type d_eq,
--   H ← tactic.get_goal, -- Get the current goal to be shown
--   -- Try to match the left of the goal equality to `oa_left`.
--   (do `(oracle_comp.support %%oa = %%s) ← tactic.infer_type H, tactic.unify oa oa_left,
--     tactic.refine ``(trans (oracle_comp.dist_equiv.support_eq %%d_eq) _)) <|>
--   -- Try to match the right of the goal equality to `oa_left`.
--   (do `(%%s = oracle_comp.support %%oa) ← tactic.infer_type H, tactic.unify oa oa_left,
--     tactic.refine ``(trans _ (oracle_comp.dist_equiv.support_eq %%d_eq).symm)) <|> return ()
-- }

/-- Attempt to discharge a distributional equivalence between two computations by todo. -/
meta def pairwise_dist_equiv_base (d_eqs : list expr) : tactic unit :=
do {
  `(%%oa ≃ₚ %%oa') ← tactic.target <|> tactic.fail ("Goal must be a distributional equivalence"),

  -- Get the type of the type of the computations being compared
  `(oracle_comp %%spec %%α) ← tactic.infer_type oa,

  -- Immedeately discharge the goal if the equivalence is between equal objects
  (tactic.unify oa oa' >> tactic.congr) <|>
    (d_eqs.mmap (λ d_eq, tactic.try (tactic.apply d_eq))
      >> return ())
}

/-- Destruct a distributional equivalence by recursively splitting equivalences between binds
into multiple equivalences between their individual components.
For other equivalences will defer to `pairwise_dist_equiv_base`. -/
meta def destruct_pairwise_dist_equiv (d_eq : list expr) : expr → tactic unit
| `((%%oa >>= %%ob ≃ₚ %%oa' >>= %%ob')) := do {

  -- Check that both portions of the bind operation
  `(oracle_comp %%spec %%α) ← tactic.infer_type oa,
  `(oracle_comp %%spec %%α') ← tactic.infer_type oa',

  do {tactic.unify α α,
    -- Split the goal into two seperate distributional equivalences.
    tactic.refine ``(oracle_comp.bind_dist_equiv_bind_of_dist_equiv _ _),

    -- Attempt to recursively solve the first equivalence.
    tactic.intros,
    tactic.target >>= destruct_pairwise_dist_equiv,

    -- Switch to the second equivalence and attempt to solve it.
    tactic.rotate 1,
    tactic.intros,
    tactic.target >>= destruct_pairwise_dist_equiv
  } <|> pairwise_dist_equiv_base d_eq
}
| _ := pairwise_dist_equiv_base d_eq

/-- Tactic for reducing proofs of distributional equivalences between bind operations
into pairwise proofs of equivalences between each component.
Attempts to discharge trivial goals using both `congr` and the given equivalences. -/
meta def pairwise_dist_equiv (d : parse texpr) : tactic unit :=
do d_eq ← tactic.i_to_expr d,
  tactic.target >>= destruct_pairwise_dist_equiv [d_eq]

example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
begin
  pairwise_dist_equiv h,
end

example (oa : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : α → β → oracle_comp spec α)
  (h : ∀ a, ob a ≃ₚ ob' a) (h' : ∀ a b, oc a b ≃ₚ oc' a b) :
  ((oa >>= λ x, ob x >>= λ y, oc x y) >>= λ x, ob x >>= λ y, oc x y) ≃ₚ
    ((oa >>= λ x, ob x >>= λ y, oc' x y) >>= λ x, ob' x >>= λ y, oc' x y) :=
begin
  pairwise_dist_equiv h;
    apply h'
end

example (oa : oracle_comp spec α) (oa' : oracle_comp spec γ)
  (ob : α → oracle_comp spec β) (ob' : γ → oracle_comp spec β)
  (h : oa >>= ob ≃ₚ oa' >>= ob') :
  oa >>= ob ≃ₚ oa' >>= ob' :=
begin
  pairwise_dist_equiv h,
end

end tactic.interactive