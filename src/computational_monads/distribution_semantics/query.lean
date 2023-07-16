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

open oracle_spec fintype
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec': oracle_spec} (i : spec.ι) (i' : spec'.ι)
  (t : spec.domain i) (u : spec.range i) (e : set (spec.range i))

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
lemma prob_output_query_eq_div : ⁅= u | query i t⁆ = 1 / ↑(card $ spec.range i) :=
by rw [prob_output, eval_dist_query, pmf.uniform_of_fintype_apply, one_div]

lemma prob_output_query_eq_inv : ⁅= u | query i t⁆ = (↑(card $ spec.range i))⁻¹ :=
by rw [prob_output, eval_dist_query, pmf.uniform_of_fintype_apply]

@[simp] lemma prob_output_query_mul_card : ⁅= u | query i t⁆ * ↑(card $ spec.range i) = 1 :=
(prob_output_query_eq_inv i t u).symm ▸ (ennreal.inv_mul_cancel (by simp) (by simp))

@[simp] lemma card_mul_prob_output_query : ↑(card $ spec.range i) * ⁅= u | query i t⁆ = 1 :=
by rw [mul_comm, prob_output_query_mul_card]

end eval_dist

section prob_event

@[simp] lemma prob_event_query_eq_div [decidable_pred (∈ e)] :
  ⁅e | query i t⁆ = ↑(card e) / ↑(card (spec.range i)) :=
by simp only [prob_event.def, eval_dist_query, pmf.to_outer_measure_uniform_of_fintype_apply,
  card_of_finset, finset.filter_congr_decidable]

lemma prob_event_query_eq_mul_inv [decidable_pred (∈ e)] :
  ⁅e | query i t⁆ = ↑(card e) * (↑(card (spec.range i)))⁻¹ :=
by simp only [prob_event.def, eval_dist_query, pmf.to_outer_measure_uniform_of_fintype_apply,
  div_eq_mul_inv, card_of_finset, finset.filter_congr_decidable]

lemma prob_event_query_eq_inv_mul [decidable_pred (∈ e)] :
  ⁅e | query i t⁆ = (↑(card (spec.range i)))⁻¹ * ↑(card e) :=
by rw [prob_event_query_eq_mul_inv, mul_comm]

lemma prob_event_query_mul_card [decidable_pred (∈ e)]:
  ⁅e | query i t⁆ * ↑(card $ spec.range i) = card e :=
by rw [prob_event_query_eq_mul_inv, mul_assoc, ennreal.inv_mul_cancel _ _, mul_one]; simp

lemma card_mul_prob_event_query [decidable_pred (∈ e)]:
  ↑(card $ spec.range i) * ⁅e | query i t⁆ = card e :=
by rw [mul_comm, prob_event_query_mul_card]

lemma prob_event_coe_finset_eq_div (e : finset (spec.range i)) :
  ⁅↑e | query i t⁆ = e.card / (card (spec.range i)) :=
by simp_rw [prob_event_query_eq_div, finset.coe_sort_coe, card_coe]

end prob_event

section query_eq_iff

lemma eval_dist_query_eq_iff (p : pmf (spec.range i)) : ⁅query i t⁆ = p ↔ ∀ x x', p x = p x' :=
begin
  simp only [eval_dist_query, pmf.ext_iff, pmf.uniform_of_fintype_apply],
  refine ⟨λ h, λ x x', (h x).symm.trans (h x'), λ h x, _⟩,
  { have hc : (((finset.univ : finset (spec.range i)).card) : ℝ≥0∞) ≠ 0,
    from nat.cast_ne_zero.2 (finset.card_ne_zero_of_mem (finset.mem_univ x)),
    have : ∑ x' : spec.range i, p x = 1 := (tsum_eq_sum (λ x' hx',
      (hx' (finset.mem_univ _)).elim)).symm.trans (trans (tsum_congr (h x)) p.tsum_coe),
    rw [finset.sum_const, nsmul_eq_mul] at this,
    rw [inv_eq_one_div, ← this, card, mul_comm, mul_div_assoc,
      ennreal.div_self hc (ennreal.nat_ne_top _), mul_one] }
end

/-- A computation is distributionally equivalent to query iff all outcomes are equally likely. -/
lemma query_dist_equiv_iff (oa : oracle_comp spec' (spec.range i)) :
  query i t ≃ₚ oa ↔ ∀ u u', ⁅= u | oa⁆ = ⁅= u' | oa⁆ := (eval_dist_query_eq_iff i t _)

lemma prob_output_query_eq_iff (r : ℝ≥0∞) : ⁅= u | query i t⁆ = r ↔ ↑(card $ spec.range i) = r⁻¹ :=
by rw [prob_output_query_eq_inv, inv_eq_iff_eq_inv]

lemma prob_output_query_eq_iff_mul_right_eq_one (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ r * (card $ spec.range i) = 1 :=
begin
  rw [prob_output_query_eq_inv],
  refine ⟨λ h, _, λ h, _⟩,
  { rw [← h, ennreal.inv_mul_cancel]; simp },
  { calc (↑(card (spec.range i)))⁻¹ = 1 * (↑(card (spec.range i)))⁻¹ : by simp
      ... = r * (↑(card (spec.range i))) * (↑(card (spec.range i)))⁻¹ : by rw [← h]
      ... = r : by rw [mul_assoc, ennreal.mul_inv_cancel, mul_one]; simp }
end

lemma prob_output_query_eq_iff_mul_left_eq_one (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ ↑(card $ spec.range i) * r = 1 :=
by rw [← mul_comm r, prob_output_query_eq_iff_mul_right_eq_one]

lemma prob_event_query_eq_iff [decidable_pred (∈ e)] (r : ℝ≥0∞) :
  ⁅e | query i t⁆ = r ↔ ↑(card e) = r * card (spec.range i) :=
begin
  rw [prob_event_query_eq_mul_inv],
  exact ⟨λ h, by rw [← h, mul_assoc, ennreal.inv_mul_cancel, mul_one]; simp,
    λ h, by rw [h, mul_assoc, ennreal.mul_inv_cancel, mul_one]; simp⟩
end

end query_eq_iff

section query_eq_zero

lemma prob_output_query_ne_zero : ⁅= u | query i t⁆ ≠ 0 :=
by simp only [prob_output_query_eq_inv, one_div, ne.def, ennreal.inv_eq_zero,
  ennreal.nat_ne_top, not_false_iff]

lemma prob_event_query_eq_zero_iff : ⁅e | query i t⁆ = 0 ↔ e = ∅ :=
by rw [prob_event_eq_zero_iff_disjoint_support, support_query, set.univ_disjoint]

lemma prob_event_query_ne_zero_of_mem (x : spec.range i) (h : x ∈ e) : ⁅e | query i t⁆ ≠ 0 :=
begin
  simp [ne.def, prob_event_eq_zero_iff_disjoint_support, support_query,
    set.disjoint_univ, set.eq_empty_iff_forall_not_mem],
  exact ⟨x, h⟩
end

end query_eq_zero

section query_eq_one

lemma prob_output_query_eq_one_iff : ⁅= u | query i t⁆ = 1 ↔ card (spec.range i) = 1 :=
begin
  simp [card_eq_one_iff],
  refine ⟨λ h, ⟨u, h⟩, λ h y, let ⟨u', h⟩ := h in (h y).trans (h u).symm⟩
end

lemma prob_event_query_eq_one_iff : ⁅e | query i t⁆ = 1 ↔ e = set.univ :=
by simp [set.univ_subset_iff, prob_event_eq_one_iff_support_subset, support_query, set.top_eq_univ]

lemma prob_event_query_ne_one_of_not_mem (x : spec.range i) (h : x ∉ e) : ⁅e | query i t⁆ ≠ 1 :=
begin
  rw [ne.def, prob_event_eq_one_iff_support_subset, support_query, set.not_subset],
  exact ⟨x, set.mem_univ x, h⟩,
end

end query_eq_one

section query_pos

@[simp] lemma prob_output_query_pos : 0 < ⁅= u | query i t⁆ :=
pos_iff_ne_zero.2 (prob_output_query_ne_zero i t u)

@[simp] lemma prob_event_query_pos_iff : 0 < ⁅e | query i t⁆ ↔ e ≠ ∅ :=
pos_iff_ne_zero.trans (by simp only [ne.def, prob_event_query_eq_zero_iff])

end query_pos

section query_eq_query

@[simp, simp_dist_equiv] lemma query_dist_equiv_query (t t' : spec.domain i) :
  query i t ≃ₚ query i t' := dist_equiv.def.2 rfl

lemma eval_dist_query_eq_eval_dist_query (t t' : spec.domain i) : ⁅query i t⁆ = ⁅query i t'⁆ := rfl

lemma prob_output_query_eq_eval_dist_query_apply_iff (t : spec.domain i) (t' : spec'.domain i')
  (u : spec.range i) (u' : spec'.range i') : ⁅= u | query i t⁆ = ⁅= u' | query i' t'⁆ ↔
    card (spec.range i) = card (spec'.range i') :=
by simp only [prob_output_query_eq_div, one_div, inv_inj, nat.cast_inj]

lemma prob_event_query_eq_prob_event_query_iff (t : spec.domain i) (t' : spec'.domain i')
  (e : set (spec.range i)) (e' : set (spec'.range i')) [decidable_pred (∈ e)]
  [decidable_pred (∈ e')] : ⁅e | query i t⁆ = ⁅e' | query i' t'⁆ ↔
    card (spec'.range i') * card e = card (spec.range i) * card e' :=
by rw [prob_event_query_eq_div, prob_event_query_eq_div, ennreal.div_eq_div_iff,
  ← nat.cast_mul, ← nat.cast_mul, nat.cast_inj]; simp

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

lemma prob_output_query_bind_eq_tsum : ⁅= x | query i t >>= oa⁆ =
  (∑' u, ⁅= x | oa u⁆) / (card $ spec.range i) :=
by simp_rw [prob_output_bind_eq_tsum, prob_output_query_eq_inv,
  ennreal.tsum_mul_left, div_eq_mul_inv, mul_comm]

lemma prob_output_query_bind_eq_sum (x : α) : ⁅= x | query i t >>= oa⁆ =
  (∑ u, ⁅= x | oa u⁆) / (card $ spec.range i) :=
by simp_rw [prob_output_bind_eq_sum, prob_output_query_eq_inv,
  ← finset.mul_sum, div_eq_mul_inv, mul_comm]

lemma prob_event_query_bind_eq_tsum (e' : set α) : ⁅e' | query i t >>= oa⁆ =
  (∑' x, ⁅e' | oa x⁆) / card (spec.range i) :=
by simp_rw [prob_event_bind_eq_tsum, prob_output_query_eq_inv,
  ennreal.tsum_mul_left, div_eq_mul_inv, mul_comm]

lemma prob_event_query_bind_eq_sum (e' : set α) : ⁅e' | query i t >>= oa⁆ =
  (∑ x, ⁅e' | oa x⁆) / card (spec.range i) :=
by simp_rw [prob_event_bind_eq_sum, prob_output_query_eq_inv,
  ← finset.mul_sum, div_eq_mul_inv, mul_comm]

end query_bind

section query_bind_return

variables (f : spec.range i → α) (x : α)

lemma support_query_bind_return : (query i t >>= λ u, return (f u)).support = set.range f :=
by simp

lemma mem_support_query_bind_return_iff : x ∈ (query i t >>= λ u, return (f u)).support ↔
  ∃ u, f u = x := by rw [support_query_bind_return, set.mem_range]

end query_bind_return

end oracle_comp