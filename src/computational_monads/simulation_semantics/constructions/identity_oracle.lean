/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_tracking

/-!
# Identity Simulation Oracle

This file defines a stateless simulation oracle `identity_oracle spec`, denoted `idₛₒ`, that
simulates a computation by making no changes (equivalently replacing queries with themselves).
This is mainly useful when appending simulation oracles and only simulating some of them.
-/

open oracle_comp oracle_spec sim_oracle prod

variables {α β γ : Type} {spec : oracle_spec}

/-- Simulation oracle for preserving the current oracle queries as is.
Can be combined with other simulation oracles to preserve some subset of queries,
e.g. `so ++ₛₒ idₛₒ` will simulate the left side oracles and preserve right side oracles. -/
def identity_oracle (spec : oracle_spec) : sim_oracle spec spec unit :=
tracking_oracle (λ _ _ _ _, ())

notation `idₛₒ` := identity_oracle _

lemma identity_oracle.def : identity_oracle spec = tracking_oracle (λ _ _ _ _, ()) := rfl

instance identity_oracle.is_tracking : (identity_oracle spec).is_tracking :=
tracking_oracle.is_tracking _

namespace identity_oracle

@[simp] lemma apply_eq {i : spec.ι} (t : spec.domain i) (s : unit) :
  idₛₒ i (t, s) = do {u ← query i t, return (u, ())} := rfl

variables (oa : oracle_comp spec α) (s : unit)

@[simp] lemma simulate'_eq_self : simulate' idₛₒ oa s = oa :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { refl },
  { simp_rw [simulate'_bind, simulate_query, apply_eq, bind_assoc, hoa, oracle_comp.return_bind] }
end

@[simp] lemma simulate_eq_self : simulate idₛₒ oa s = do {x ← oa, return (x, ())} :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { rw [simulate_return, oracle_comp.return_bind, punit_eq s ()] },
  { simp_rw [simulate_bind, simulate_query, apply_eq, bind_assoc, oracle_comp.return_bind, hoa] }
end

end identity_oracle