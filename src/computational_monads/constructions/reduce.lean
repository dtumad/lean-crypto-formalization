/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad
import computational_monads.tactics

/-!
# Reducing Return Statements in Computation

This file defines a function `oracle_comp.reduce` that removes extra return statements by
immedeately substituting the return value to the next computation.
The resulting computation isn't definitionally equal to the original, but both
are equivalent under the probabalistic denotational semantics (see `oracle_comp.reduce_equiv`)
-/

namespace oracle_comp

open oracle_spec

variables {α β : Type} {spec : oracle_spec}

/-- Simplify portions of the computation that just return a value.
In particular recursively replace `return x >>= ob` with `ob x`, which doesn't change the
probabilistic semantics of the computation (see `oracle_comp.reduce_equiv`). -/
def reduce : Π {α : Type}, oracle_comp spec α → oracle_comp spec α
| _ (pure' α a) := pure' α a
| _ (bind' α β (pure' _ a) ob) := ob a
| _ (bind' _ β (query i t) ob) := bind' _ _ (query i t) ob
| _ (bind' α β oa ob) := bind' α β (reduce oa) (λ x, reduce (ob x))
| _ (query i t) := query i t

theorem reduce_equiv (oa : oracle_comp spec α) : oa.reduce ≃ₚ oa :=
begin
  oracle_comp.default_induction `oa,
  { exact rfl },
  {
    oracle_comp.default_induction `oa,
    {
      refine trans _ (eval_dist_return_bind _ _).symm,
      exact rfl,
    },
    {
      sorry,
    },
    {
      exact rfl,
    }
  },
  { exact rfl }
end

end oracle_comp