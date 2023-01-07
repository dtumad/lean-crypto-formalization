/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.stateless_oracle
import computational_monads.constructions.uniform_select

/-!
# Uniform Oracles

This file defines a simulation oracle called `uniform_oracle`,
that reduces any computation to one with a `uniform_selecting` `oracle_spec`,
by responding uniformly at random to any query.
-/

open oracle_comp oracle_spec ennreal

variables {α β : Type} {spec : oracle_spec}

noncomputable def uniform_oracle (spec : oracle_spec) :
  sim_oracle spec uniform_selecting unit :=
⟪λ i t, $ᵗ (spec.range i)⟫

lemma uniform_oracle.def (spec : oracle_spec) :
  uniform_oracle spec = ⟪λ i t, $ᵗ (spec.range i)⟫ := rfl

namespace uniform_oracle

variables (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i) (u : unit)

@[simp] lemma apply_eq : uniform_oracle spec i (t, u) =
  $ᵗ (spec.range i) >>= λ u, return (u, ()) := rfl

noncomputable instance decidable_apply : oracle_comp.decidable (uniform_oracle spec i (t, u)) :=
stateless_oracle.decidable _ i (t, u)

section support

@[simp] lemma support_apply : (uniform_oracle spec i (t, u)).support = ⊤ :=
by simp only [uniform_oracle.def, stateless_oracle.support_apply,
  support_uniform_select_fintype, set.top_eq_univ, set.preimage_univ]

@[simp] lemma fin_support_apply : (uniform_oracle spec i (t, u)).fin_support = ⊤ :=
by rw [fin_support_eq_iff_support_eq_coe, support_apply,
  finset.top_eq_univ, finset.coe_univ, set.top_eq_univ]

end support

section eval_dist

end eval_dist

end uniform_oracle