/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_comp

/-!
# Running Compuations With No Oracles

This file defines a function `run_comp` for "running" an `oracle_comp` that doesn't have access to
any oracles, where `empty_spec` is used to represent the lack of available oracles.
In this case the `oracle_comp.query` constructor can't be called, and so we can eliminate this
case and perform the natural reduction on other computations.

TODO: Should be possible to generalize this to use `random_gen`, allowing greater flexibility.
-/

namespace oracle_comp

open oracle_spec

/-- Run a computation with `[]ₒ` as the oracles, using `empty.elim` in the `query` case. -/
def run_comp : Π {α : Type}, oracle_comp []ₒ α → α
| _ (pure' α a) := a
| _ (bind' α β oa ob) := let a : α := run_comp oa in run_comp (ob a)
| _ (query i t) := empty.elim i

variables {α β : Type} (oa : oracle_comp []ₒ α) (ob : α → oracle_comp []ₒ β) (a : α) (b : β)

@[simp] lemma run_comp_return : run_comp (return a) = a := rfl

@[simp] lemma run_comp_bind : run_comp (oa >>= ob) = run_comp (ob $ run_comp oa) := rfl

lemma run_comp_query (i : []ₒ.ι) (t : []ₒ.domain i) (u : []ₒ.range i) : run_comp (query i t) = u :=
empty.elim i

example : run_comp
(do { x ← return 1,
      y ← return (x + 1),
      z ← return (x * y + y * x),
      return (y + y = z) }) = true := -- Check that `2 + 2 = 4`
by simp only [run_comp_bind, run_comp_return, one_mul, mul_one, eq_self_iff_true]

end oracle_comp