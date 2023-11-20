/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.map
import computational_monads.distribution_semantics.query

/-!
# Computations With Probabalistic Oracles

This file defines a type `prob_comp spec α` for computations with a uniform selection oracle,
as an alias for `oracle_comp (unif_spec ++ spec) α`.
-/

variables {α β γ : Type}

open oracle_spec

/-- Shorthand for a computation that has a single oracle, allowing uniformly random sampling.
Writting as a inlined expression to avoid needing lemma duplications with regular `oracle_comp`. -/
@[inline, reducible] def prob_comp (spec : oracle_spec) (α : Type) : Type 1 :=
oracle_comp (unif_spec ++ spec) α

namespace prob_comp



end prob_comp