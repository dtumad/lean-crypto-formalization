/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.push_map_dist_equiv
import to_mathlib.mprod

/-!
# Distribution Semantics of Sequence Operation

This file contains lemmas about the distribution semantics of `<*>`, which can be use
to combine two computations with some operation.
For example given `oa ob : oracle_comp spec ℕ`, `(+) <$> oa <*> ob` is the computation that
runs `oa` and `ob` independently to get `x` and `y`, returning the sum `x + y`.
-/

namespace oracle_comp

open oracle_spec
open_locale ennreal big_operators

variables {α β γ δ : Type} {spec spec' : oracle_spec}

example (n : oracle_comp spec ℕ) :
(+) <$> (return 0) <*> n ≃ₚ n :=
begin
  push_map_dist_equiv,
  rw_dist_equiv [return_bind_dist_equiv],
  simp,
  simp_rw [zero_add_eq_id],
  rw_dist_equiv [bind_return_id_dist_equiv],
end

end oracle_comp