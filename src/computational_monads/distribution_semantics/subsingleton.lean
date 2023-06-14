/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.map

/-!
# Distribution Semantics of Computations on Subsingleton Types

This file gives various lemmas for probabilities of computations `oa : oracle_comp spec α`,
when `α` is a subsingleton type, simplifying many computations.
-/


namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- If a type `α` is `subsingleton` then any pair of computations are distributionally equivalent,
so in particular they must necessarilly be just `return oa.default_result`. -/
@[simp, simp_dist_equiv]
lemma dist_equiv_of_subsingleton [subsingleton α] (oa : oracle_comp spec α)
  (oa' : oracle_comp spec' α) : oa ≃ₚ oa' := subsingleton.elim _ _

end oracle_comp