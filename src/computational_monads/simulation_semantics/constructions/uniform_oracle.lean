/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_stateless

/-!
# Uniform Oracles

This file defines a simulation oracle called `uniformₛₒ` that reduces any computation to
one with only a `uniform_selecting` oracle by responding uniformly at random to any query.
Because of the way `eval_dist` is defined this doesn't change the associated distribution,
only the representation in terms of oracles available.
The main use case is in later defining random oracles (see `randomₛₒ`).
-/

open oracle_comp oracle_spec sim_oracle prod

variables {α β : Type} {spec : oracle_spec}

@[inline, reducible] noncomputable def uniform_oracle (spec : oracle_spec) :
  sim_oracle spec uniform_selecting unit := ⟪λ i t, $ᵗ (spec.range i)⟫

notation `uniformₛₒ` := uniform_oracle _

lemma uniform_oracle.def : uniformₛₒ = ⟪λ i t, $ᵗ (spec.range i)⟫ := rfl

instance uniform_oracle.is_stateless : (uniform_oracle spec).is_stateless :=
stateless_oracle.is_stateless _

namespace uniform_oracle

lemma apply_eq {i : spec.ι} (t : spec.domain i) (s : unit) :
  uniformₛₒ i (t, s) = ($ᵗ (spec.range i) ×ₘ return ()) := rfl

lemma answer_query_eq {i : spec.ι} (t : spec.domain i) :
  (uniform_oracle spec).answer_query i t = fst <$> ($ᵗ (spec.range i) ×ₘ return ()) := rfl

lemma answer_query_dist_equiv {i : spec.ι} (t : spec.domain i) :
  (uniform_oracle spec).answer_query i t ≃ₚ $ᵗ (spec.range i) := by pairwise_dist_equiv

lemma update_state_eq : (uniform_oracle spec).update_state = λ _ _ _ _, () := rfl

section simulate'

variables (oa : oracle_comp spec α) (s : unit)

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' uniformₛₒ oa s ≃ₚ oa :=
is_tracking.simulate'_dist_equiv_self uniformₛₒ oa s
  (λ i t, by rw_dist_equiv [stateless_oracle.answer_query_dist_equiv,
      oracle_comp.uniform_select_fintype_range t])

@[simp] lemma support_simulate' : (simulate' uniformₛₒ oa s).support = oa.support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_simulate' [decidable_eq α] :
  (simulate' uniformₛₒ oa s).fin_support = oa.fin_support :=
by pairwise_dist_equiv

@[simp] lemma eval_dist_simulate' : ⁅simulate' uniformₛₒ oa s⁆ = ⁅oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_output_simulate' (x : α) : ⁅= x | simulate' uniformₛₒ oa s⁆ = ⁅= x | oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_simulate' (e : set α) : ⁅e | simulate' uniformₛₒ oa s⁆ = ⁅e | oa⁆ :=
by pairwise_dist_equiv

end simulate'

section simulate

variables (oa : oracle_comp spec α) (s : unit)

@[pairwise_dist_equiv] lemma simulate_dist_equiv : simulate uniformₛₒ oa s ≃ₚ (oa ×ₘ return ()) :=
is_stateless.simulate_dist_equiv_self uniformₛₒ oa s
  (λ i t, by rw_dist_equiv [stateless_oracle.answer_query_dist_equiv,
    uniform_select_fintype_range t])

@[simp] lemma support_simulate : (simulate uniformₛₒ oa s).support = oa.support ×ˢ {()} :=
is_stateless.support_simulate_eq_support uniformₛₒ oa s (by simp)

@[simp] lemma fin_support_simulate [decidable_eq α] :
  (simulate uniformₛₒ oa s).fin_support = oa.fin_support ×ˢ {()} :=
is_stateless.fin_support_simulate_eq_fin_support uniformₛₒ oa s (by simp)

@[simp] lemma eval_dist_simulate : ⁅simulate uniformₛₒ oa s⁆ = ⁅oa ×ₘ return ()⁆ :=
is_stateless.eval_dist_simulate_eq_eval_dist uniformₛₒ oa s (by simp)

@[simp] lemma prob_output_simulate (z : α × unit) : ⁅= z | simulate uniformₛₒ oa s⁆ = ⁅= z.1 | oa⁆ :=
is_stateless.prob_output_simulate_eq_prob_output uniformₛₒ oa s (by simp [prob_output_query_eq_inv]) z

@[simp] lemma prob_event_simulate (e : set (α × unit)) :
  ⁅e | simulate uniformₛₒ oa s⁆ = ⁅fst '' e | oa⁆ :=
is_stateless.prob_event_simulate_eq_prob_event uniformₛₒ oa s (by simp [prob_output_query_eq_inv]) e

end simulate

end uniform_oracle