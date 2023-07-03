/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad

/-!
# Distributional Semantics of Simulation of a Pair of Computations

This file contains lemmas about simulation semantics interactions with `simulate`
-/

variables {α β γ : Type} {spec spec' : oracle_spec} {S : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables (so : sim_oracle spec spec' S) (a : α) (s : S)

-- lemma simulate'_product_dist_equiv

end oracle_comp