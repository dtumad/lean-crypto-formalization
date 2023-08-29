/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.map
import computational_monads.distribution_semantics.tactics.rw_dist_equiv

/-!
# Induction Tactics for Pushing a Map Operation into Bind Operation

This file defines a tactic `push_map_dist_equiv` for pushing a map operation inside sequenced
compuations when trying to prove equivalence between computations.
-/

open interactive interactive.types

namespace oracle_comp

/-- Push map operations into bind and return operations. Calls into `simp_dist_equiv` rather
than an independent implementation, avoiding replicating the recursion.
Optional arguments can be used to provide a list of additional lemmas to use,
and to specify the maximum recursion depth (default `3` for efficiency). -/
@[interactive] meta def push_map_dist_equiv
  (opt_d_eqs : parse (optional (pexpr_list)))
  (opt_iters : parse (optional lean.parser.small_nat)) :=
do map_lemmas ← return [`oracle_comp.map_bind_dist_equiv,
    `oracle_comp.map_return_dist_equiv',
    `oracle_comp.map_return_dist_equiv],
  t' ← mmap tactic.get_decl map_lemmas,
  d ←  return (list.map declaration.value t'),
  q ← return (list.map pexpr.of_expr d ++ (opt_d_eqs.get_or_else [])),
  simp_dist_equiv tt (some q) (some (opt_iters.get_or_else 3)),
  tactic.try by_dist_equiv

end oracle_comp

section tests

variables {α β γ δ ε: Type} {spec spec' : oracle_spec}

/-- `push_map_dist_equiv` should be able to push into a `return` operation. -/
example (x : α) (f : α → β) : f <$> (return x : oracle_comp spec α) ≃ₚ
  (return (f x) : oracle_comp spec β) :=
by push_map_dist_equiv

/-- `push_map_dist_equiv` should be able to handle differeing `oracle_spec`. -/
example (x : α) (f : α → β) : f <$> (return x : oracle_comp spec α) ≃ₚ
  (return (f x) : oracle_comp spec' β) :=
by push_map_dist_equiv

/-- `push_map_dist_equiv` should work if the map is written as a bind. -/
example (x : α) (f : α → β) : f <$> (return x : oracle_comp spec α) ≃ₚ
  (return (f x) : oracle_comp spec β) :=
by { rw [oracle_comp.map_eq_bind_return_comp], push_map_dist_equiv }

/-- `push_map_dist_equiv` should work if the map is written as a bind. -/
example (x : α) (f : α → β) : f <$> (return x : oracle_comp spec α) ≃ₚ
  f <$> (return x : oracle_comp spec' α) :=
by push_map_dist_equiv

/-- `push_map_dist_equiv` should be able to push into an inverted `return` operation. -/
example (x : α) (f : α → β) : (return (f x) : oracle_comp spec β) ≃ₚ
  f <$> (return x : oracle_comp spec α) :=
by push_map_dist_equiv

/-- `push_map_dist_equiv` should be able to push into two `return` operations. -/
example (x : α) (f : α → γ) (y : β) (g : β → γ) (h : f x = g y) :
  f <$> (return x : oracle_comp spec α) ≃ₚ g <$> (return y : oracle_comp spec β) :=
by { push_map_dist_equiv, simp only [function.comp_app, h] }

example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (f : β → γ) :
  f <$> (do {x ← oa, ob x}) ≃ₚ do {x ← oa, f <$> ob x} :=
by push_map_dist_equiv

example (oa : oracle_comp spec α) (g : α → β) (f : β → γ) :
  f <$> (do {x ← oa, return (g x)}) ≃ₚ do {x ← oa, return (f (g x))} :=
by push_map_dist_equiv

example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ)
  (f : γ → δ) : f <$> (do {x ← oa, y ← ob x, oc x y}) ≃ₚ do {x ← oa, y ← ob x, f <$> (oc x y)} :=
by push_map_dist_equiv

example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (g : α → β → γ) (f : γ → δ) :
  f <$> (do {x ← oa, y ← ob x, return (g x y)}) ≃ₚ
    do {x ← oa, y ← ob x, return (f (g x y))} :=
by push_map_dist_equiv

example (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (oc : α → β → oracle_comp spec γ) (od : α → β → γ → oracle_comp spec δ) (f : δ → ε) :
  f <$> (do {x ← oa, y ← ob x, z ← oc x y, od x y z}) ≃ₚ
    do {x ← oa, y ← ob x, z ← oc x y, f <$> od x y z} :=
by push_map_dist_equiv

end tests
