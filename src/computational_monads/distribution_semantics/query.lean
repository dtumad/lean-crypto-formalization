/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.equiv

/-!
# Distribution Semantics of Queries

This file gives various lemmas for probabilities outcomes of the computation `query i t`.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec': oracle_spec} (i : spec.ι) (i' : spec'.ι)

section query_eq_iff

/-- A computation is distributionally equivalent to query iff all outcomes are equally likely. -/
lemma query_dist_equiv_iff (t : spec.domain i) (oa : oracle_comp spec' (spec.range i)) :
  query i t ≃ₚ oa ↔ ∀ u u', ⁅= u | oa⁆ = ⁅= u' | oa⁆ :=
begin
  refine ⟨λ h u u', by simp only [← h.eval_dist_eq, eval_dist_query_apply], λ h, _⟩,
  simp only [dist_equiv.ext_iff, eval_dist_query_apply],
  intro x,
  have : ∑ x' : spec.range i, ⁅oa⁆ x = 1,
  by calc ∑ x' : spec.range i, ⁅oa⁆ x = ∑ x' : spec.range i, ⁅oa⁆ x' : finset.sum_congr rfl (λ x' _, h x x')
    ... = 1 : by simp_rw [sum_eq_tsum_indicator, finset.coe_univ, set.indicator_univ, pmf.tsum_coe],
  rw [finset.sum_const, nsmul_eq_mul] at this,
  rw [← this, fintype.card, mul_comm, mul_div_assoc, ennreal.div_self, mul_one],
  { rw [nat.cast_ne_zero],
    refine finset.card_ne_zero_of_mem (finset.mem_univ x) },
  { simp only [ne.def, ennreal.nat_ne_top, not_false_iff] }
end

-- lemma eval_dist_query_eq_iff (t : spec.domain i) (p : pmf (spec.range i)) :
--   ⁅query i t⁆ = p ↔ ∀ x x', p x = p x' :=
-- begin
--   rw [eval_dist_query],
--   simp [pmf.ext_iff],
-- end

lemma eval_dist_query_apply_eq_iff (t : spec.domain i) (u : spec.range i) (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ ↑(fintype.card $ spec.range i) = r⁻¹ :=
by rw [eval_dist_query_apply_eq_inv, inv_eq_iff_eq_inv]

lemma eval_dist_query_apply_eq_iff_mul_eq_one (t : spec.domain i) (u : spec.range i) (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ r * (fintype.card $ spec.range i) = 1 :=
begin
  by_cases hr0 : r = 0,
  {
    simp only [hr0, eval_dist_query, pmf.uniform_of_fintype_apply, ennreal.inv_eq_zero, ennreal.nat_ne_top, zero_mul, zero_ne_one],
  },
  {
    by_cases hr : r = ⊤,
    {
      simp only [hr, eval_dist_query, pmf.uniform_of_fintype_apply, ennreal.inv_eq_top, nat.cast_eq_zero,
        fintype.card_eq_zero_iff, ennreal.top_mul, not_is_empty_of_nonempty, nat.cast_eq_zero, false_iff],
      split_ifs; simp
    },
    {
      rw [eval_dist_query_apply_eq_iff, inv_eq_one_div],
      rw [ennreal.eq_div_iff hr0 hr],
    }
  }
end

end query_eq_iff

lemma prob_event_coe_finset (t : spec.domain i) (e : finset (spec.range i)) :
  ⁅↑e | query i t⁆ = e.card / (fintype.card (spec.range i)) :=
by simp_rw [prob_event_query, finset.coe_sort_coe, fintype.card_coe]

lemma eval_dist_query_apply_ne_zero (t : spec.domain i) (u : spec.range i) :
  ⁅= u | query i t⁆ ≠ 0 :=
by simp only [eval_dist_query_apply, one_div, ne.def, ennreal.inv_eq_zero,
  ennreal.nat_ne_top, not_false_iff]

lemma prob_event_query_eq_zero_iff (t : spec.domain i) (e : set (spec.range i)) :
  ⁅e | query i t⁆ = 0 ↔ e = ∅ :=
by rw [prob_event_eq_zero_iff_disjoint_support, support_query, set.top_eq_univ, set.univ_disjoint]


lemma eval_dist_query_apply_eq_one_iff (t : spec.domain i) (u : spec.range i) :
  ⁅= u | query i t⁆ = 1 ↔ fintype.card (spec.range i) = 1 :=
begin
  simp only [eval_dist_query, pmf.uniform_of_fintype_apply, ← one_div],
  exact trans (ennreal.div_eq_one_iff (nat.cast_ne_zero.2 fintype.card_ne_zero) $
    ennreal.nat_ne_top _) (eq_comm.trans nat.cast_eq_one),
end

lemma prob_event_query_eq_one_iff (t : spec.domain i) (e : set (spec.range i)) :
  ⁅e | query i t⁆ = 1 ↔ e = set.univ :=
by simp only [set.univ_subset_iff, prob_event_eq_one_iff_support_subset,
  support_query, set.top_eq_univ]

lemma eval_dist_query_apply_pos (t : spec.domain i) (u : spec.range i) : 0 < ⁅= u | query i t⁆ :=
pos_iff_ne_zero.2 (eval_dist_query_apply_ne_zero i t u)

lemma prob_event_query_pos_iff (t : spec.domain i) (e : set (spec.range i)) :
  0 < ⁅e | query i t⁆ ↔ e ≠ ∅ :=
pos_iff_ne_zero.trans (by simp only [ne.def, prob_event_query_eq_zero_iff])

@[simp] lemma query_dist_equiv_query (t t' : spec.domain i) :
  query i t ≃ₚ query i t' := dist_equiv.def.2 rfl

lemma eval_dist_query_eq_eval_dist_query (t t' : spec.domain i) : ⁅query i t⁆ = ⁅query i t'⁆ := rfl

lemma eval_dist_query_apply_eq_eval_dist_query_apply_iff (t : spec.domain i) (t' : spec'.domain i')
  (u : spec.range i) (u' : spec'.range i') : ⁅= u | query i t⁆ = ⁅= u' | query i' t'⁆ ↔
    fintype.card (spec.range i) = fintype.card (spec'.range i') :=
by simp only [eval_dist_query_apply, one_div, inv_inj, nat.cast_inj]

-- lemma prob_event_query_eq_prob_event_query_iff (t : spec.domain i) (t' : spec'.domain i')
--   (e : set (spec.range i)) (e' : set (spec'.range i')) : ⁅e | query i t⁆ = ⁅e' | query i' t'⁆ ↔



end oracle_comp