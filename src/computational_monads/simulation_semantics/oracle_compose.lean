/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.simulation_semantics.constructions.identity_oracle

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
def compose (so' : sim_oracle spec' spec'' S') (so : sim_oracle spec spec' S) : sim_oracle spec spec'' (S × S') :=
λ i x, simulate so' (so i (x.1, x.2.1)) x.2.2 >>= λ u_s, return (u_s.1.1, u_s.1.2, u_s.2)

-- We use `notation` over `infixl` to swap the arguments without invoking `function.comp`.
notation so' `∘ₛₒ` so := so'.compose so

namespace oracle_compose

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec' spec'' S')

@[simp] lemma apply_eq (i : spec.ι) (z : spec.domain i × S × S') : (so' ∘ₛₒ so) i z =
  simulate so' (so i (z.1, z.2.1)) z.2.2 >>= λ z', return (z'.1.1, z'.1.2, z'.2) := rfl

instance is_tracking (so : sim_oracle spec spec S) (so' : sim_oracle spec spec S')
  [hso : so.is_tracking] [hso' : so'.is_tracking] : (so' ∘ₛₒ so).is_tracking :=
⟨λ i t s, by rw [apply_eq, fst_map_bind_return, ← map_map_eq_map_comp _ prod.fst prod.fst,
  ← simulate', is_tracking.simulate'_eq_self, is_tracking.fst_map_apply_eq_query]⟩

end oracle_compose

end sim_oracle