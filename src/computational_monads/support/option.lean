/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.support.monad

/-!
# Support of Computations Involving Prod

This file contains lemmas about `support` and `fin_support` focused on working with `option` types.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec} (oa : oracle_comp spec α)

end oracle_comp