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

-- TODO: merge the matching
meta def destruct_dist_equiv : expr → tactic unit
-- Trying to prove equivalence between two binding operations
| `((%%oa >>= %%ob ≃ₚ %%oa' >>= %%ob')) := do {
  tactic.trace ("Reducing a bind operation"),

  -- Check that both portions of the bind operation
  `(oracle_comp %%spec %%α) ← tactic.infer_type oa,
  `(oracle_comp %%spec %%α') ← tactic.infer_type oa',
  tactic.unify α α' <|> tactic.trace "failed to unify the two first parts",

  tactic.refine ``(oracle_comp.bind_dist_equiv_bind_of_dist_equiv _ _),

  return ()
}
| `(%%oa ≃ₚ %%oa') := do {
  tactic.trace ("Reducing " ++ (to_string oa) ++ " and " ++ (to_string oa')),

  -- Get the type of the type of the computations being compared
  `(oracle_comp %%spec %%α) ← tactic.infer_type oa,

  -- Immedeately discharge the goal if the equivalence is between equal objects
  tactic.unify oa oa' >> tactic.congr <|>
    tactic.trace "Nothing happened",

  return ()
}
| _ := return ()

meta def pairwise_dist_equiv : tactic unit :=
do {
  G ← tactic.get_goal,
  g ← tactic.infer_type G,
  destruct_dist_equiv g
}

example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
begin
  pairwise_dist_equiv,

end


-- meta def reduce_support_expr (d_eq : expr) : expr → tactic (expr)
-- | `(oracle_comp.support (oracle_comp.bind' %%α %%β %%oa %%ob)) :=
--   do {
--     tactic.trace "Found a bind': " >> return (reflect ()),
--     tactic.trace ("first part - " ++ to_string oa),
--     ob_body ← return ob.lambda_body,
--     tactic.trace ("second part - " ++ to_string ob_body),

--     test ← reduce_support_expr ob_body,
--     return (reflect ())
--   }
-- | `(oracle_comp.support (%%oa >>= %%ob)) :=
--   do {
--     tactic.trace "Found a bind: " >> return (reflect ()),
--     tactic.trace ("first part - " ++ to_string oa),
--     ob_body ← return ob.lambda_body,
--     tactic.trace ("second part - " ++ to_string ob_body),


--     test ← reduce_support_expr ob_body,
--     return (reflect ())
--   }
-- -- | `(oracle_comp.support %%oa) :=
-- --   do {
-- --     tactic.unify oa oa_left >> tactic.trace "unified" >> return oa_right
-- --       <|> tactic.trace "didn't unify" >> return oa
-- --   }
-- | e := tactic.trace ("stuck with: " ++ to_string e) >> return (reflect ())


-- /-- Using a given equivalence `d : oa ≃ₚ oa'`, check if the goal is an equality with
-- `oa.support` on either side, and if so replace it with `oa'.support`. -/
-- meta def rw_support_base_goal' (d : parse texpr) : tactic unit :=
-- do {
--   d_eq ← tactic.i_to_expr d, -- Get the left and right sides of the distributional equivalence.
--   `(oracle_comp.dist_equiv %%oa_left %%oa_right) ← tactic.infer_type d_eq,
--   H ← tactic.get_goal, -- Get the left and right sides of the equality
--   h ← tactic.infer_type H,
--   match h with
--   | `(%%e1 = %%e2) := do {
--     e1' ← reduce_support_expr d_eq e1,


--     -- e2' ← reduce_support_expr d_eq e2,
--     return ()

--     -- tactic.trace ("Results from both sides: " ++ to_string e1' ++ " and " ++ to_string e2')
--   }
--   | `(%%e) := do {
--     e' ← reduce_support_expr d_eq e,
--     return ()
--     -- tactic.trace ("Result from reduction: " ++ to_string e)
--   }
--   end
-- }


-- example (oa oa' oa'' : oracle_comp spec α) (h : oa ≃ₚ oa') (h' : oa' ≃ₚ oa'')
--   (test : oa'.support = oa''.support) (ob : α → oracle_comp spec β)
--   (ob' : oracle_comp spec β) (h'' : ob' ≃ₚ (oa >>= ob)) :
--   (oa >>= ob).support = ob'.support :=
-- begin
--   rw_support_base_goal' h'',
--   sorry,
-- end

-- example (oa oa' : oracle_comp spec α) (ob : α → oracle_comp spec β)
--   (oc : α → β → oracle_comp spec γ) (h : oa ≃ₚ oa') (s : γ → Prop) :
--   (do {x ← oa, y ← ob x, oc x y}).support = s :=
-- begin
--   rw_support_base_goal' h
-- end




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

-- meta def rw_support (q : parse texpr) : parse location → tactic unit
-- | (loc.ns [some h]) := tactic.trace "Doesn't yet support rewriting at other locations"
-- | (loc.ns [none]) := rw_support_base_goal q
-- | _ := tactic.trace "No rewriting to do"


-- -- meta def rw_dist_equiv_core (d : parse texpr) : tactic unit :=
-- -- do {
-- --   d_eq ← tactic.i_to_expr d,
-- --   `(oracle_comp.dist_equiv %%oa_left %%oa_right) ← tactic.infer_type d_eq,
-- --   support_eq ← return ``(oracle_comp.dist_equiv.support_eq %%d_eq),
-- --   simp_rw _ _
-- -- }

-- meta def simp_rw_dist_equiv (q : parse texpr) (l : parse location) : tactic unit :=
-- simp_rw begin

-- end l
-- -- q.rules.mmap' (λ rule, do
-- --   let simp_arg := if rule.symm
-- --     then simp_arg_type.symm_expr rule.rule
-- --     else simp_arg_type.expr rule.rule,
-- --   save_info rule.pos,
-- --   simp none none tt [simp_arg] [] l)



-- end tactic.interactive

-- example (oa oa' oa'' : oracle_comp spec α) (h : oa ≃ₚ oa') (h' : oa' ≃ₚ oa'')
--   (test : oa'.support = oa''.support) :
--   oa.support = oa''.support :=
-- begin
--   simp_rw_dist_equiv h at ⊢,
-- end

-- #check tactic.rewrite









-- meta def tactic.interactive.rewrite_support_base (q : parse texpr) : parse location → tactic unit
-- | (loc.ns [some h]) := do {
--   -- Get the distributional equivalence argument and its type
--   d_eq ← tactic.i_to_expr q,
--   `(oracle_comp.dist_equiv %%oa_left %%oa_right) ← tactic.infer_type d_eq,
--   -- Get the type of the goal
--   H ← tactic.get_local h,
--   `(oracle_comp.support %%oa = %%s) ← tactic.infer_type H,


--   -- Check if we're trying to calculate the support of `oa_left`.
--   _ ← tactic.unify oa oa_left,

--   «have» h ``(oracle_comp.support %%oa_right = %%s)
--     ``(trans (oracle_comp.dist_equiv.support_eq %%d_eq).symm %%H),
--   tactic.clear H
-- }
-- | _ := tactic.fail "done"