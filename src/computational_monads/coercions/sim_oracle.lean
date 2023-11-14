/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.oracle_append

/-!
# Coercions Between Simulation Oracles With Target Spec Coercions

This file provides a number of `has_coe` instances for `sim_oracle`, when the
target `oracle_spec` already defines computations with coercions,
using the coercion to respond to oracle queries in the new set of oracles.
-/

namespace oracle_comp

open oracle_spec

variables (spec spec' spec'' spec''' : oracle_spec)
  (coe_spec coe_spec' coe_spec'' coe_spec''' : oracle_spec)
  (S S' : Type) {α : Type}

section coe_sim_oracle

/-- Use a coercion on the resulting type of a simulation to coerce the simulation oracle itself.
  This allows for greater flexibility when specifying the simulation oracle when
    both the initial and final `oracle_spec` are some appended set of oracles -/
noncomputable instance [coe_spec ⊂ₒ coe_spec'] :
  has_coe (sim_oracle spec coe_spec S) (sim_oracle spec coe_spec' S) :=
⟨λ so, {default_state := so.default_state, o := λ i x, ↑(so i x)}⟩

/-- Coerce a simulation oracle to include an additional number of resulting oracles -/
noncomputable example (so : sim_oracle coe_spec coe_spec' S) :
  sim_oracle coe_spec (coe_spec' ++ spec ++ spec') S := ↑so

/-- Can use coercions to seperately simulate both sides of appended oracle specs -/
noncomputable example (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec''' S') :
  sim_oracle (spec ++ spec') (spec'' ++ spec''') (S × S') :=
↑so ++ₛ ↑so'

end coe_sim_oracle

end oracle_comp