/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.oracle_compose

/-!
# Appending Simulation Oracles

This file defines an append operation `++ₛₒ` for simulation oracles,
creating a simulation oracle for a combined set of initial oracles.
In particular, if simulation oracles `so` and `so'` have starting oracles given by
`spec` and `spec'`, then `so ++ₛₒ so'` will have starting oracles `spec ++ spec'`.

The implementation just maintains a seperate state for each oracle,
using pattern matching on queries to decide which `sim_oracle` to call.

TODO: This has all been moved to the main file for now
-/

-- open oracle_comp oracle_spec sum

-- variables {spec spec' spec'' spec''' : oracle_spec} {α β γ : Type} {S S' : Type}

-- namespace sim_oracle

-- def append (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S') :
--   sim_oracle (spec ++ spec') spec'' (S × S') :=
-- λ i, match i with
-- | (inl i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₁'⟩ ← so i (t, s₁), return (u, s₁', s₂)}
-- | (inr i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₂'⟩ ← so' i (t, s₂), return (u, s₁, s₂')}
-- end

-- infixl ` ++ₛₒ `:65 := append

-- variables (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S')

-- @[simp] lemma append_apply_inl (i : spec.ι) (x : spec.domain i × S × S') :
--   (so ++ₛₒ so') (inl i) x = (λ z : spec.range i × S, (z.1, z.2, x.2.2)) <$> so i (x.1, x.2.1) :=
-- begin
--   rcases x with ⟨t, s₁, s₂⟩,
--   refine congr_arg (λ ou, so i (t, s₁) >>= ou) (funext $ λ y, _),
--   cases y, refl,
-- end

-- @[simp] lemma append_apply_inr (i : spec'.ι) (x : spec'.domain i × S × S') :
--   (so ++ₛₒ so') (inr i) x = (λ z : spec'.range i × S', (z.1, x.2.1, z.2)) <$> so' i (x.1, x.2.2) :=
-- begin
--   rcases x with ⟨t, s₁, s₂⟩,
--   refine congr_arg (λ ou, so' i (t, s₂) >>= ou) (funext $ λ y, _),
--   cases y, refl,
-- end

-- end sim_oracle