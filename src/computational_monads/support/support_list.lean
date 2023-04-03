/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.support.support

/-!
# List of a Computation's Possible Outputs.

This file defines a function `oracle_comp.support_list : oracle_comp spec α → list α`,
that returns a list of the possible outputs of a computation.
-/

namespace oracle_comp

variables {α β : Type} {spec : oracle_spec}

open_locale classical

noncomputable def support_list : Π {α : Type}, oracle_comp spec α → finset α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := finset.bUnion (support_list oa) (λ x, support_list (ob x))
| _ (query i t) := finset.univ


end oracle_comp