/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad

/-!
# Distribution Semantics of Queries

This file gives various lemmas for probabilities outcomes of the computation `query i t`.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec': oracle_spec} (i : spec.ι) (i' : spec'.ι)
  (t : spec.domain i) (t' : spec'.domain i') (u : spec.range i) (u' : spec'.range i')
  (e : set (spec.range i)) (e' : set (spec'.range i'))

section mem_support

/-- Any element is a possible output of `query`. -/
lemma mem_support_query : u ∈ (query i t).support := set.mem_univ u

lemma mem_fin_support_query : u ∈ (query i t).fin_support := finset.mem_univ u

lemma mem_support_query_iff_true : u ∈ (query i t).support ↔ true :=
by simp only [support_query, set.top_eq_univ, set.mem_univ]

lemma mem_fin_support_query_iff_true : u ∈ (query i t).fin_support ↔ true :=
by simp only [fin_support_query, finset.mem_univ]

end mem_support

section eval_dist

/-- The chance of getting a result `u` from `query i t` is uniform over the output type. -/
lemma eval_dist_query_apply_eq_div : ⁅= u | query i t⁆ = 1 / (fintype.card $ spec.range i) :=
by rw [eval_dist_query, pmf.uniform_of_fintype_apply, one_div]

lemma eval_dist_query_apply_eq_inv : ⁅= u | query i t⁆ = (fintype.card $ spec.range i)⁻¹ :=
by rw [eval_dist_query, pmf.uniform_of_fintype_apply]

@[simp] lemma prob_event_query_eq_div [decidable_pred (∈ e)] :
  ⁅e | query i t⁆ = fintype.card e / fintype.card (spec.range i) :=
by simp only [prob_event.def, eval_dist_query, pmf.to_outer_measure_uniform_of_fintype_apply,
  fintype.card_of_finset, finset.filter_congr_decidable]

lemma prob_event_query_eq_mul_inv [decidable_pred (∈ e)] :
  ⁅e | query i t⁆ = fintype.card e * (fintype.card (spec.range i))⁻¹ :=
sorry

lemma prob_event_query_eq_inv_mul [decidable_pred (∈ e)] :
  ⁅e | query i t⁆ = (fintype.card (spec.range i))⁻¹ * fintype.card e :=
sorry

lemma prob_event_coe_finset_eq_div (e : finset (spec.range i)) :
  ⁅↑e | query i t⁆ = e.card / (fintype.card (spec.range i)) :=
by simp_rw [prob_event_query_eq_div, finset.coe_sort_coe, fintype.card_coe]


end eval_dist

section query_eq_iff

lemma eval_dist_query_eq_iff (t : spec.domain i) (p : pmf (spec.range i)) :
  ⁅query i t⁆ = p ↔ ∀ x x', p x = p x' :=
begin
  simp only [eval_dist_query, pmf.ext_iff, pmf.uniform_of_fintype_apply],
  refine ⟨λ h, λ x x', (h x).symm.trans (h x'), λ h x, _⟩,
  { have hc : (((finset.univ : finset (spec.range i)).card) : ℝ≥0∞) ≠ 0,
    from nat.cast_ne_zero.2 (finset.card_ne_zero_of_mem (finset.mem_univ x)),
    have : ∑ x' : spec.range i, p x = 1 := (tsum_eq_sum (λ x' hx',
      (hx' (finset.mem_univ _)).elim)).symm.trans (trans (tsum_congr (h x)) p.tsum_coe),
    rw [finset.sum_const, nsmul_eq_mul] at this,
    rw [inv_eq_one_div, ← this, fintype.card, mul_comm, mul_div_assoc,
      ennreal.div_self hc (ennreal.nat_ne_top _), mul_one] }
end

lemma eval_dist_query_apply_eq_iff (t : spec.domain i) (u : spec.range i) (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ ↑(fintype.card $ spec.range i) = r⁻¹ :=
by rw [eval_dist_query_apply_eq_inv, inv_eq_iff_eq_inv]

lemma eval_dist_query_apply_eq_iff_mul_right_eq_one (t : spec.domain i) (u : spec.range i) (r : ℝ≥0∞) :
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

lemma eval_dist_query_apply_eq_iff_mul_left_eq_one (t : spec.domain i) (u : spec.range i) (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ ↑(fintype.card $ spec.range i) * r = 1 :=
by rw [← mul_comm r, eval_dist_query_apply_eq_iff_mul_right_eq_one]


/-- A computation is distributionally equivalent to query iff all outcomes are equally likely. -/
lemma query_dist_equiv_iff (t : spec.domain i) (oa : oracle_comp spec' (spec.range i)) :
  query i t ≃ₚ oa ↔ ∀ u u', ⁅= u | oa⁆ = ⁅= u' | oa⁆ :=
begin
  refine ⟨λ h u u', by simp only [← h.eval_dist_eq, eval_dist_query_apply_eq_div], λ h, _⟩,
  simp only [dist_equiv.ext_iff, eval_dist_query_apply_eq_div],
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

end query_eq_iff



section query_eq_zero

lemma eval_dist_query_apply_ne_zero (t : spec.domain i) (u : spec.range i) :
  ⁅= u | query i t⁆ ≠ 0 :=
by simp only [eval_dist_query_apply_eq_div, one_div, ne.def, ennreal.inv_eq_zero,
  ennreal.nat_ne_top, not_false_iff]

lemma prob_event_query_eq_zero_iff (t : spec.domain i) (e : set (spec.range i)) :
  ⁅e | query i t⁆ = 0 ↔ e = ∅ :=
by rw [prob_event_eq_zero_iff_disjoint_support, support_query, set.top_eq_univ, set.univ_disjoint]

end query_eq_zero



section query_eq_one

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

end query_eq_one

section query_pos

lemma eval_dist_query_apply_pos (t : spec.domain i) (u : spec.range i) : 0 < ⁅= u | query i t⁆ :=
pos_iff_ne_zero.2 (eval_dist_query_apply_ne_zero i t u)

lemma prob_event_query_pos_iff (t : spec.domain i) (e : set (spec.range i)) :
  0 < ⁅e | query i t⁆ ↔ e ≠ ∅ :=
pos_iff_ne_zero.trans (by simp only [ne.def, prob_event_query_eq_zero_iff])

end query_pos


section query_eq_query

@[simp] lemma query_dist_equiv_query (t t' : spec.domain i) :
  query i t ≃ₚ query i t' := dist_equiv.def.2 rfl

lemma eval_dist_query_eq_eval_dist_query (t t' : spec.domain i) : ⁅query i t⁆ = ⁅query i t'⁆ := rfl

lemma eval_dist_query_apply_eq_eval_dist_query_apply_iff (t : spec.domain i) (t' : spec'.domain i')
  (u : spec.range i) (u' : spec'.range i') : ⁅= u | query i t⁆ = ⁅= u' | query i' t'⁆ ↔
    fintype.card (spec.range i) = fintype.card (spec'.range i') :=
by simp only [eval_dist_query_apply_eq_div, one_div, inv_inj, nat.cast_inj]

end query_eq_query





section query_bind

variables (oa : spec.range i → oracle_comp spec α) (x : α)

lemma support_query_bind : (query i t >>= oa).support = ⋃ u, (oa u).support :=
by simp_rw [support_bind, set.Union_true]

lemma mem_support_query_bind_iff : x ∈ (query i t >>= oa).support ↔ ∃ t, x ∈ (oa t).support :=
by rw [support_query_bind, set.mem_Union]

lemma fin_support_query_bind [decidable_eq α] : (query i t >>= oa).fin_support =
  finset.bUnion finset.univ (λ u, (oa u).fin_support) :=
by {simp only [fin_support_bind, fin_support_query, finset.top_eq_univ], congr}

lemma mem_fin_support_query_bind_iff [decidable_eq α] :
  x ∈ (query i t >>= oa).fin_support ↔ ∃ t, x ∈ (oa t).fin_support :=
by simp only [fin_support_query_bind, finset.mem_bUnion, finset.mem_univ, exists_true_left]

lemma eval_dist_query_bind_apply_eq_tsum :
  ⁅= x | query i t >>= oa⁆ = (∑' u, ⁅= x | oa u⁆) / (fintype.card $ spec.range i) :=
by simp_rw [eval_dist_bind_apply_eq_tsum, eval_dist_query_apply_eq_inv,
  ennreal.tsum_mul_left, div_eq_mul_inv, mul_comm]

lemma eval_dist_query_bind_apply_eq_sum :
  ⁅query i t >>= oa⁆ x = (∑ u, ⁅oa u⁆ x) / (fintype.card $ spec.range i) :=
by simp_rw [eval_dist_bind_apply_eq_sum, eval_dist_query_apply_eq_inv,
  ← finset.mul_sum, div_eq_mul_inv, mul_comm]

lemma prob_event_query_bind_eq_tsum (e' : set α) :
  ⁅e' | query i t >>= oa⁆ = (∑' x, ⁅e' | oa x⁆) / fintype.card (spec.range i) :=
by simp_rw [prob_event_bind_eq_tsum, eval_dist_query_apply_eq_inv,
  ennreal.tsum_mul_left, div_eq_mul_inv, mul_comm]

lemma prob_event_query_bind_eq_sum (e' : set α) :
  ⁅e' | query i t >>= oa⁆ = (∑ x, ⁅e' | oa x⁆) / fintype.card (spec.range i) :=
by simp_rw [prob_event_bind_eq_sum, eval_dist_query_apply_eq_inv,
  ← finset.mul_sum, div_eq_mul_inv, mul_comm]

end query_bind

end oracle_comp