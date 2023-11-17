/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_stateless

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
@[inline, reducible] def identity_oracle (spec : oracle_spec) :
  sim_oracle spec spec unit := ⟪query⟫

notation `idₛₒ` := identity_oracle _

lemma identity_oracle.def : identity_oracle spec = ⟪query⟫ := rfl

instance identity_oracle.is_stateless : (identity_oracle spec).is_stateless :=
stateless_oracle.is_stateless query

namespace identity_oracle

lemma apply_eq {i : spec.ι} (t : spec.domain i) (s : unit) :
  idₛₒ i (t, s) = (query i t ×ₘ return ()) := rfl

lemma answer_query_eq {i : spec.ι} (t : spec.domain i) :
  (identity_oracle spec).answer_query i t = fst <$> (query i t ×ₘ return ()) := rfl

lemma update_state_eq : (identity_oracle spec).update_state = λ _ _ _ _, () := rfl

section simulate'

variables (oa : oracle_comp spec α) (s : unit)

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' idₛₒ oa s ≃ₚ oa :=
is_tracking.simulate'_dist_equiv_self idₛₒ oa s
  (λ i t, stateless_oracle.answer_query_dist_equiv _ _)

@[simp] lemma support_simulate' : (simulate' idₛₒ oa s).support = oa.support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_simulate' [decidable_eq α] :
  (simulate' idₛₒ oa s).fin_support = oa.fin_support :=
by pairwise_dist_equiv

@[simp] lemma eval_dist_simulate' : ⁅simulate' idₛₒ oa s⁆ = ⁅oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_output_simulate' (x : α) : ⁅= x | simulate' idₛₒ oa s⁆ = ⁅= x | oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_simulate' (e : set α) : ⁅e | simulate' idₛₒ oa s⁆ = ⁅e | oa⁆ :=
by pairwise_dist_equiv

end simulate'

section simulate

variables (oa : oracle_comp spec α) (s : unit)

@[pairwise_dist_equiv] lemma simulate_dist_equiv : simulate idₛₒ oa s ≃ₚ (oa ×ₘ return ()) :=
is_stateless.simulate_dist_equiv_self idₛₒ oa s
  (λ i t, stateless_oracle.answer_query_dist_equiv _ _)

@[simp] lemma support_simulate : (simulate idₛₒ oa s).support = oa.support ×ˢ {()} :=
is_stateless.support_simulate_eq_support idₛₒ oa s (by simp)

@[simp] lemma fin_support_simulate [decidable_eq α] : (simulate idₛₒ oa s).fin_support = oa.fin_support ×ˢ {()} :=
is_stateless.fin_support_simulate_eq_fin_support idₛₒ oa s (by simp)

@[simp] lemma eval_dist_simulate : ⁅simulate idₛₒ oa s⁆ = ⁅oa ×ₘ return ()⁆ :=
is_stateless.eval_dist_simulate_eq_eval_dist idₛₒ oa s (by simp)

@[simp] lemma prob_output_simulate (z : α × unit) : ⁅= z | simulate idₛₒ oa s⁆ = ⁅= z.1 | oa⁆ :=
is_stateless.prob_output_simulate_eq_prob_output idₛₒ oa s (by simp [prob_output_query_eq_inv]) z

@[simp] lemma prob_event_simulate (e : set (α × unit)) :
  ⁅e | simulate idₛₒ oa s⁆ = ⁅fst '' e | oa⁆ :=
is_stateless.prob_event_simulate_eq_prob_event idₛₒ oa s (by simp [prob_output_query_eq_inv]) e

end simulate

end identity_oracle