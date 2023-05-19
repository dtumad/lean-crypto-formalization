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
open_locale ennreal big_operators

variables {α β : Type} {spec : oracle_spec}

noncomputable def uniform_oracle (spec : oracle_spec) :
  sim_oracle spec uniform_selecting unit :=
⟪λ i t, $ᵗ (spec.range i)⟫

lemma uniform_oracle.def (spec : oracle_spec) :
  uniform_oracle spec = ⟪λ i t, $ᵗ (spec.range i)⟫ := rfl

namespace uniform_oracle

variables (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i) (s : unit)

@[simp] lemma apply_eq : uniform_oracle spec i (t, s) =
  $ᵗ (spec.range i) >>= λ u, return (u, ()) := rfl

section support

@[simp] lemma support_apply : (uniform_oracle spec i (t, s)).support = ⊤ :=
by simp only [uniform_oracle.def, stateless_oracle.support_apply,
  support_uniform_select_fintype, set.top_eq_univ, set.preimage_univ]

@[simp] lemma fin_support_apply : (uniform_oracle spec i (t, s)).fin_support = ⊤ :=
by rw [fin_support_eq_iff_support_eq_coe, support_apply,
  finset.top_eq_univ, finset.coe_univ, set.top_eq_univ]

@[simp] lemma support_simulate :
  (simulate (uniform_oracle spec) oa s).support = prod.fst ⁻¹' oa.support :=
stateless_oracle.support_simulate_eq_preimage_support oa _ s
  (λ i t, support_uniform_select_fintype _)

@[simp] lemma support_simulate' : (simulate' (uniform_oracle spec) oa s).support = oa.support :=
stateless_oracle.support_simulate'_eq_support oa _ s (λ i t, support_uniform_select_fintype _)

end support

section eval_dist

@[simp] lemma eval_dist_apply :
  ⁅uniform_oracle spec i (t, s)⁆ = pmf.uniform_of_fintype (spec.range i × unit) :=
begin
  refine pmf.ext (λ x, _),
  rw [apply_eq, eval_dist_bind_return, eval_dist_uniform_select_fintype, pmf.map_apply],
  refine trans (tsum_eq_single x.1 $ λ u hu, _) _,
  { simp only [prod.eq_iff_fst_eq_snd_eq, hu.symm, false_and, if_false] },
  { simp only [prod.eq_iff_fst_eq_snd_eq, eq_self_iff_true, true_and, punit_eq x.2 (), if_true,
      pmf.uniform_of_fintype_apply, fintype.card_prod, fintype.card_unit, mul_one] }
end

end eval_dist

section prob_event

@[simp] lemma prob_event_apply (e : set (spec.range i × unit)) [decidable_pred e] :
  ⁅e | uniform_oracle spec i (t, s)⁆ = fintype.card e / fintype.card (spec.range i) :=
calc ⁅e | uniform_oracle spec i (t, s)⁆
  = (∑' x, e.indicator 1 x) / fintype.card (spec.range i) : begin
    rw [apply_eq, prob_event_uniform_select_fintype_bind_eq_tsum],
    simp only [prob_event_return, set.indicator, pi.one_apply,
      ennreal.tsum_prod'],
    have : ∀ u, ∑' (s : unit), ite ((u, s) ∈ e) (1 : ℝ≥0∞) 0 = ite ((u, ()) ∈ e) 1 0,
    from λ u, tsum_eq_single () (λ s' hs', (hs' $ punit_eq _ _).elim),
    congr,
    refine funext (λ u, _),
    specialize this u,
    convert this.symm,
    refine funext (λ s, _),
    split_ifs; refl
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