/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_stateless

/-!
# Uniform Oracles

This file defines a simulation oracle called `uniformₛₒ`,
that reduces any computation to one with a `uniform_selecting` `oracle_spec`,
by responding uniformly at random to any query.
-/

open oracle_comp oracle_spec
open_locale ennreal big_operators

variables {α β : Type} {spec : oracle_spec}

noncomputable def uniform_oracle (spec : oracle_spec) :
  sim_oracle spec uniform_selecting unit := ⟪λ i t, $ᵗ (spec.range i)⟫

notation `uniformₛₒ` := uniform_oracle _

lemma uniform_oracle.def (spec : oracle_spec) : uniformₛₒ = ⟪λ i t, $ᵗ (spec.range i)⟫ := rfl

noncomputable instance uniform_oracle.is_stateless : (uniform_oracle spec).is_stateless :=
stateless_oracle.is_stateless _

namespace uniform_oracle

open sim_oracle

variables (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i) (s : unit) (u : spec.range i)

@[simp] lemma apply_eq : uniformₛₒ i (t, s) = ($ᵗ (spec.range i) ×ₘ return ()) := rfl

@[pairwise_dist_equiv]
lemma answer_query_dist_equiv : (uniform_oracle spec).answer_query i t ≃ₚ $ᵗ (spec.range i) :=
stateless_oracle.answer_query_dist_equiv _ _

lemma update_state_eq : (uniform_oracle spec).update_state s i t u = () := subsingleton.elim _ _

section answer_query

@[simp] lemma support_answer_query : ((uniform_oracle spec).answer_query i t).support = set.univ :=
trans ((answer_query_dist_equiv i t).support_eq) (support_uniform_select_fintype _)

@[simp] lemma fin_support_answer_query : ((uniform_oracle spec).answer_query i t).fin_support = finset.univ :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_univ, support_answer_query]

end answer_query

section apply

@[simp] lemma support_apply : (uniformₛₒ i (t, s)).support = set.univ :=
by rw [sim_oracle.is_stateless.support_apply, support_answer_query, set.preimage_univ]

@[simp] lemma fin_support_apply : (uniformₛₒ i (t, s)).fin_support = finset.univ :=
by rw [fin_support_eq_iff_support_eq_coe, support_apply, finset.coe_univ]

end apply

section simulate'

@[simp] lemma support_simulate' : (simulate' uniformₛₒ oa s).support = oa.support :=
is_tracking.support_simulate'_eq_support _ oa s (λ i t, support_answer_query i t)

end simulate'

section simulate

@[simp] lemma support_simulate : (simulate uniformₛₒ oa s).support = oa.support ×ˢ {()} :=
is_stateless.support_simulate_eq_support _ oa s (λ i t, support_answer_query i t)

end simulate

section support

end support

section eval_dist

@[simp] lemma eval_dist_apply :
  ⁅uniformₛₒ i (t, s)⁆ = pmf.uniform_of_fintype (spec.range i × unit) :=
begin
  refine trans (is_stateless.eval_dist_apply _ _ _) _,
  sorry,
  -- rw [uniformₛₒ_def],
  -- rw [stateless_oracle.eval_dist_answer_query],
  -- refine pmf.ext (λ x, _),
  -- rw [apply_eq, eval_dist_bind_return, eval_dist_uniform_select_fintype, pmf.map_apply],
  -- refine trans (tsum_eq_single x.1 $ λ u hu, _) _,
  -- { simp only [prod.eq_iff_fst_eq_snd_eq, hu.symm, false_and, if_false] },
  -- { simp only [prod.eq_iff_fst_eq_snd_eq, eq_self_iff_true, true_and, punit_eq x.2 (), if_true,
  --     pmf.uniform_of_fintype_apply, fintype.card_prod, fintype.card_unit, mul_one] }
end

end eval_dist

section prob_event

@[simp] lemma prob_event_apply (e : set (spec.range i × unit)) [decidable_pred e] :
  ⁅e | uniformₛₒ i (t, s)⁆ = fintype.card e / fintype.card (spec.range i) :=
calc ⁅e | uniformₛₒ i (t, s)⁆
  = (∑' x, e.indicator 1 x) / fintype.card (spec.range i) : begin
    sorry,
    -- rw [apply_eq, prob_event_uniform_select_fintype_bind_eq_tsum],
    -- simp only [prob_event_return, set.indicator, pi.one_apply,
    --   ennreal.tsum_prod'],
    -- have : ∀ u, ∑' (s : unit), ite ((u, s) ∈ e) (1 : ℝ≥0∞) 0 = ite ((u, ()) ∈ e) 1 0,
    -- from λ u, tsum_eq_single () (λ s' hs', (hs' $ punit_eq _ _).elim),
    -- congr,
    -- refine funext (λ u, _),
    -- specialize this u,
    -- convert this.symm,
    -- refine funext (λ s, _),
    -- split_ifs; refl
  end
  ... = (∑ x, e.indicator 1 x) / fintype.card (spec.range i) : begin
    congr,
    refine tsum_eq_sum (λ y h, (h $ finset.mem_univ y).elim),
  end
  ... = fintype.card e / fintype.card (spec.range i) : begin
    congr,
    rw finset.sum_indicator_eq_sum_filter,
    simp only [pi.one_apply, finset.sum_const, nat.smul_one_eq_coe, fintype.card_of_finset],
  end

end prob_event

end uniform_oracle