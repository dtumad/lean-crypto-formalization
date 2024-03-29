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

variables {α β γ : Type} {spec spec': oracle_spec}

section support

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

/-- Any element is a possible output of `query`. -/
lemma mem_support_query : u ∈ (query i t).support :=
by simp only [support_query]

lemma mem_fin_support_query : u ∈ (query i t).fin_support :=
by simp only [fin_support_query, finset.mem_univ]

lemma mem_support_query_iff_true : u ∈ (query i t).support ↔ true :=
by simp only [support_query, set.top_eq_univ, set.mem_univ]

lemma mem_fin_support_query_iff_true : u ∈ (query i t).fin_support ↔ true :=
by simp only [fin_support_query, finset.mem_univ]

end support

section eval_dist

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

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

variables (i : spec.ι) (t : spec.domain i) (p : spec.range i → Prop)

@[simp] lemma prob_event_query_eq_div [decidable_pred p] :
  ⁅p | query i t⁆ = ↑(card {x | p x}) / ↑(card (spec.range i)) :=
by simpa only [prob_event.def, eval_dist_query, pmf.to_outer_measure_uniform_of_fintype_apply,
  card_of_finset, finset.filter_congr_decidable]

lemma prob_event_query_eq_mul_inv [decidable_pred p] :
  ⁅p | query i t⁆ = ↑(card {x | p x}) * (↑(card (spec.range i)))⁻¹ :=
by rw [prob_event_query_eq_div, div_eq_mul_inv]

lemma prob_event_query_eq_inv_mul [decidable_pred p] :
  ⁅p | query i t⁆ = (↑(card (spec.range i)))⁻¹ * ↑(card {x | p x}) :=
by rw [prob_event_query_eq_mul_inv, mul_comm]

lemma prob_event_query_mul_card [decidable_pred p] :
  ⁅p | query i t⁆ * ↑(card $ spec.range i) = card {x | p x} :=
by rw [prob_event_query_eq_mul_inv, mul_assoc, ennreal.inv_mul_cancel _ _, mul_one]; simp

lemma card_mul_prob_event_query [decidable_pred p] :
  ↑(card $ spec.range i) * ⁅p | query i t⁆ = card {x | p x} :=
by rw [mul_comm, prob_event_query_mul_card]

lemma prob_event_mem_finset_query (e : finset (spec.range i)) :
  ⁅(∈ e) | query i t⁆ = e.card / (card (spec.range i)) :=
by simp only [prob_event_query_eq_div, finset.set_of_mem, finset.coe_sort_coe, card_coe]

end prob_event

section query_eq_iff

variables (i : spec.ι) (t : spec.domain i)

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

lemma prob_output_query_eq_iff (u : spec.range i) (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ ↑(card $ spec.range i) = r⁻¹ :=
by rw [prob_output_query_eq_inv, inv_eq_iff_eq_inv]

lemma prob_output_query_eq_iff_mul_right_eq_one (u : spec.range i) (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ r * (card $ spec.range i) = 1 :=
begin
  rw [prob_output_query_eq_inv],
  refine ⟨λ h, _, λ h, _⟩,
  { rw [← h, ennreal.inv_mul_cancel]; simp },
  { calc (↑(card (spec.range i)))⁻¹ = 1 * (↑(card (spec.range i)))⁻¹ : by simp
      ... = r * (↑(card (spec.range i))) * (↑(card (spec.range i)))⁻¹ : by rw [← h]
      ... = r : by rw [mul_assoc, ennreal.mul_inv_cancel, mul_one]; simp }
end

lemma prob_output_query_eq_iff_mul_left_eq_one (u : spec.range i) (r : ℝ≥0∞) :
  ⁅= u | query i t⁆ = r ↔ ↑(card $ spec.range i) * r = 1 :=
by rw [← mul_comm r, prob_output_query_eq_iff_mul_right_eq_one]

lemma prob_event_query_eq_iff (p : spec.range i → Prop) [decidable_pred p] (r : ℝ≥0∞) :
  ⁅p | query i t⁆ = r ↔ ↑(card {x | p x}) = r * card (spec.range i) :=
begin
  rw [prob_event_query_eq_mul_inv],
  exact ⟨λ h, by rw [← h, mul_assoc, ennreal.inv_mul_cancel, mul_one]; simp,
    λ h, by rw [h, mul_assoc, ennreal.mul_inv_cancel, mul_one]; simp⟩
end

end query_eq_iff

section query_eq_zero

variables (i : spec.ι) (t : spec.domain i)

lemma prob_output_query_ne_zero (u : spec.range i) : ⁅= u | query i t⁆ ≠ 0 :=
by simp only [prob_output_query_eq_inv, one_div, ne.def, ennreal.inv_eq_zero,
  ennreal.nat_ne_top, not_false_iff]

lemma prob_event_query_eq_zero_iff (p : spec.range i → Prop) :
  ⁅p | query i t⁆ = 0 ↔ ∀ x, ¬ p x :=
by simp only [prob_event_eq_zero_iff, support_query, set.mem_univ, forall_true_left]

lemma prob_event_query_ne_zero_of_mem {p : spec.range i → Prop} (x : spec.range i) 
  (h : p x) : ⁅p | query i t⁆ ≠ 0 :=
begin
  rw [ne.def, prob_event_query_eq_zero_iff, not_forall_not],
  exact ⟨x, h⟩
end

end query_eq_zero

section query_eq_one

variables (i : spec.ι) (t : spec.domain i)

lemma prob_output_query_eq_one_iff (u : spec.range i) :
  ⁅= u | query i t⁆ = 1 ↔ card (spec.range i) = 1 :=
by rw [prob_output_query_eq_inv, inv_eq_iff_eq_inv, inv_one, nat.cast_eq_one]

lemma prob_event_query_eq_one_iff (p : spec.range i → Prop) : ⁅p | query i t⁆ = 1 ↔ ∀ x, p x :=
by simp only [prob_event_eq_one_iff, support_query, set.mem_univ, forall_true_left]

lemma prob_event_query_ne_one_of_not_mem {p : spec.range i → Prop} (x : spec.range i)
  (h : ¬ p x) : ⁅p | query i t⁆ ≠ 1 :=
by simpa [ne.def, prob_event_query_eq_one_iff, not_forall] using (⟨x, h⟩ : ∃ x, ¬ p x)

end query_eq_one

section query_pos

variables (i : spec.ι) (t : spec.domain i)

@[simp] lemma prob_output_query_pos (u : spec.range i) : 0 < ⁅= u | query i t⁆ :=
pos_iff_ne_zero.2 (prob_output_query_ne_zero i t u)

@[simp] lemma prob_event_query_pos_iff (p : spec.range i → Prop) :
  0 < ⁅p | query i t⁆ ↔ ∃ x, p x :=
by rw [pos_iff_ne_zero, ne.def, prob_event_query_eq_zero_iff, not_forall_not]

end query_pos

section query_eq_query

variable (i : spec.ι)

@[simp, pairwise_dist_equiv] lemma query_dist_equiv_query (i : spec.ι) (t t' : spec.domain i) :
  query i t ≃ₚ query i t' := dist_equiv.def.2 rfl

lemma eval_dist_query_eq_eval_dist_query (t t' : spec.domain i) : ⁅query i t⁆ = ⁅query i t'⁆ := rfl

-- lemma prob_output_query_eq_eval_dist_query_apply_iff (t : spec.domain i) (t' : spec'.domain i')
--   (u : spec.range i) (u' : spec'.range i') : ⁅= u | query i t⁆ = ⁅= u' | query i' t'⁆ ↔
--     card (spec.range i) = card (spec'.range i') :=
-- by simp only [prob_output_query_eq_div, one_div, inv_inj, nat.cast_inj]

-- lemma prob_event_query_eq_prob_event_query_iff (t : spec.domain i) (t' : spec'.domain i')
--   (p : set (spec.range i)) (e' : set (spec'.range i')) [decidable_pred (∈ e)]
--   [decidable_pred (∈ e')] : ⁅e | query i t⁆ = ⁅e' | query i' t'⁆ ↔
--     card (spec'.range i') * card e = card (spec.range i) * card e' :=
-- by rw [prob_event_query_eq_div, prob_event_query_eq_div, ennreal.div_eq_div_iff,
--   ← nat.cast_mul, ← nat.cast_mul, nat.cast_inj]; simp

end query_eq_query

section query_bind

variables (i : spec.ι) (t : spec.domain i) (oa : spec.range i → oracle_comp spec α) (x : α)

lemma support_query_bind : (query i t >>= oa).support = ⋃ u, (oa u).support :=
by simp_rw [support_bind, support_query, set.Union_true]

lemma mem_support_query_bind_iff : x ∈ (query i t >>= oa).support ↔ ∃ t, x ∈ (oa t).support :=
by rw [support_query_bind, set.mem_Union]

lemma fin_support_query_bind [decidable_eq α] : (query i t >>= oa).fin_support =
  finset.bUnion finset.univ (λ u, (oa u).fin_support) :=
by {simp only [fin_support_bind, fin_support_query, finset.top_eq_univ] }

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
  ← finset.mul_sum, div_eq_mul_inv, mul_comm, fin_support_query]

lemma prob_event_query_bind_eq_tsum (p : α → Prop) : ⁅p | query i t >>= oa⁆ =
  (∑' x, ⁅p | oa x⁆) / card (spec.range i) :=
by simp_rw [prob_event_bind_eq_tsum, prob_output_query_eq_inv,
  ennreal.tsum_mul_left, div_eq_mul_inv, mul_comm]

lemma prob_event_query_bind_eq_sum (p : α → Prop) : ⁅p | query i t >>= oa⁆ =
  (∑ x, ⁅p | oa x⁆) / card (spec.range i) :=
by simp_rw [prob_event_bind_eq_sum, prob_output_query_eq_inv,
  ← finset.mul_sum, div_eq_mul_inv, mul_comm, fin_support_query]

end query_bind

end oracle_comp