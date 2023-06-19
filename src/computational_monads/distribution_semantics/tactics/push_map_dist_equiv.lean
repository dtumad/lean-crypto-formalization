/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.map

/-!
# Induction Tactics for Pushing a Map Operation into Bind Operation

This file defines a tactic `push_map_dist_equiv` for pushing a map operation inside sequenced
compuations when trying to prove equivalence between computations.
-/

open interactive interactive.types

variables {α β γ δ ε: Type} {spec : oracle_spec}

namespace oracle_comp

private meta def push_map_aux : expr → tactic (option (pexpr))
| `(%%f <$> (return %%x)) :=
  return (some (``((oracle_comp.map_return_dist_equiv %%f %%x))))
| `(%%f <$> (%%oa >>= λ _, %%ob)) := do
  sub_expr' ← tactic.to_expr ``(%%f <$> %%ob) tt ff,
  rec ← push_map_aux sub_expr',
  match rec with
  | (some (prf)) := return (some (
      ``(trans (oracle_comp.map_bind_dist_equiv %%oa (λ _, %%ob) %%f)
          (bind_dist_equiv_bind_of_dist_equiv_right' %%oa _ _ (λ _, %%prf)))))
  | none := return (some (
      ``(oracle_comp.map_bind_dist_equiv _ _ _)))
  end
| `(%%oa) := return none

/-- Push map operations on both sides of an equivalence inwards recursively.
Will also try to solve the equation reflexively at the end. -/
@[interactive] meta def push_map_dist_equiv (opt_d_eqs : parse (optional (pexpr_list))) :
  tactic unit :=
do g ← tactic.target,
match g with
| `(%%oa ≃ₚ %%oa') := do {
  x ← push_map_aux oa,
  y ← push_map_aux oa',
  match x with
  | (some x) := tactic.refine ``(trans %%x _)
  | none := tactic.refine ``(_)
  end,
  match y with
  | (some x) := tactic.refine ``(symm (trans %%x _))
  | none := tactic.refine ``(_)
  end,
  tactic.try tactic.reflexivity
}
| _ := tactic.fail "Goal must be a distributional equivalence between a map applied to a bind"
end


end oracle_comp

section tests

open oracle_comp

/-- `push_map_dist_equiv` should be able to push into a `return` operation. -/
example (x : α) (f : α → β) : f <$> (return x : oracle_comp spec α) ≃ₚ
  (return (f x) : oracle_comp spec β) :=
by push_map_dist_equiv

/-- `push_map_dist_equiv` should be able to push into an inverted `return` operation. -/
example (x : α) (f : α → β) : (return (f x) : oracle_comp spec β) ≃ₚ
  f <$> (return x : oracle_comp spec α) :=
by push_map_dist_equiv

/-- `push_map_dist_equiv` should be able to push into two `return` operations. -/
example (x : α) (f : α → γ) (y : β) (g : β → γ) (h : f x = g y) :
  f <$> (return x : oracle_comp spec α) ≃ₚ g <$> (return y : oracle_comp spec β) :=
by { push_map_dist_equiv, rw [h] }

example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (f : β → γ) :
  f <$> (do {x ← oa, ob x}) ≃ₚ do {x ← oa, f <$> ob x} :=
by push_map_dist_equiv

example (oa : oracle_comp spec α) (g : α → β) (f : β → γ) :
  f <$> (do {x ← oa, return (g x)}) ≃ₚ do {x ← oa, return (f (g x))} :=
by push_map_dist_equiv

example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ)
  (f : γ → δ) : f <$> (do {x ← oa, y ← ob x, oc x y}) ≃ₚ do {x ← oa, y ← ob x, f <$> (oc x y)} :=
by push_map_dist_equiv

-- example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (g : α → β → γ) (f : γ → δ) :
--   f <$> (do {x ← oa, y ← ob x, return (g x y)}) ≃ₚ
--     do {x ← oa, y ← ob x, return (f (g x y))} :=
-- by push_map_dist_equiv

-- example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
--   (oc : α → β → oracle_comp spec γ) (od : α → β → γ → oracle_comp spec δ) (f : δ → ε) :
--   f <$> (do {x ← oa, y ← ob x, z ← oc x y, od x y z}) ≃ₚ
--     do {x ← oa, y ← ob x, z ← oc x y, f <$> od x y z} :=
-- begin
--   push_map_dist_equiv,
-- end


end tests
