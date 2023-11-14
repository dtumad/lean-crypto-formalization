/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad

/-!
# Composition of Simulation Oracles

This file defines an operator `∘ₛ` for composing two simulation oracles in the natural way,
such that simulation corresponds to a two step simulation by both.
-/

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {α β γ : Type} {S S' : Type}

namespace sim_oracle

/-- Compose two `sim_oracles`, using the first oracle to simulate the queries of the second.
For example a random oracle is a uniform oracle composed with a cacheing oracle,
i.e. one that caches previous responses and calls a uniform random oracle for any new queries.
For type inference reasons we list the arguments in the opposite order of `function.comp`. -/
noncomputable def oracle_compose (so : sim_oracle spec spec' S)
  (so' : sim_oracle spec' spec'' S') : sim_oracle spec spec'' (S × S') :=
{ default_state := (so.default_state, so'.default_state),
  o := λ i x, simulate so' (so i (x.1, x.2.1)) x.2.2 >>= λ u_s, return (u_s.1.1, u_s.1.2, u_s.2) }

-- We use `notation` over `infixl` to swap the arguments without invoking `function.comp`.
notation so' `∘ₛ` so := oracle_compose so so'

namespace oracle_compose

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec' spec'' S')

lemma apply_eq (i : spec.ι) (s : S × S') : (so' ∘ₛ so) i =
  λ x, simulate so' (so i (x.1, x.2.1)) x.2.2 >>= λ u_s, return (u_s.1.1, u_s.1.2, u_s.2) := rfl

end oracle_compose

end sim_oracle