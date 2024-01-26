/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.seq

/-!
# Distribution Semantics of Algebra Operations

This file contains lemmas about computations where the return type has some algebraic structure.
-/

namespace oracle_comp

open oracle_spec
open_locale ennreal big_operators

variables {α β γ δ : Type} {spec spec' : oracle_spec}
  (og : oracle_comp spec (α → β)) (oa oa' : oracle_comp spec α)

section comm

@[pairwise_dist_equiv] lemma seq_map_mul_dist_equiv_comm [comm_monoid α] :
  (*) <$> oa <*> oa' ≃ₚ (*) <$> oa' <*> oa := seq_map_dist_equiv_comm oa oa' (*) mul_comm

@[pairwise_dist_equiv] lemma seq_map_add_dist_equiv_comm [add_comm_monoid α] :
  (+) <$> oa <*> oa' ≃ₚ (+) <$> oa' <*> oa := seq_map_dist_equiv_comm oa oa' (+) add_comm

end comm

section mul_one_class

@[pairwise_dist_equiv, to_additive] lemma map_mul_one [mul_one_class α] :
  ((* 1) : α → α) <$> oa ≃ₚ oa := by rw [mul_one_eq_id, id_map]

@[pairwise_dist_equiv, to_additive] lemma map_one_mul [mul_one_class α] :
  (((*) 1) : α → α) <$> oa ≃ₚ oa := by rw [one_mul_eq_id, id_map]

end mul_one_class

section is_cancel

variables [has_mul α]

@[simp, to_additive] lemma prob_output_map_mul_right [is_right_cancel_mul α] (x : α) :
  ⁅= (*) x | (*) <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_of_injective oa x (λ y y' hg, (mul_left_inj x).1 (congr_fun hg x))

@[simp, to_additive] lemma prob_output_map_mul_left [is_left_cancel_mul α] (x : α) :
  ⁅= (* x) | (λ y, (* y)) <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_of_injective oa x (λ y y' hg, (mul_right_inj x).1 (congr_fun hg x))

/-- If a multiplication has an `is_right_cancel` instance then the result of multiplying the result
of two computations has probability given by summing over only the possible first results. -/
@[simp, to_additive] lemma prob_output_seq_map_mul [is_right_cancel_mul α]
  (z : α) : ⁅= z | (*) <$> oa <*> oa'⁆ = ∑' x, ⁅(= z) ∘ (* x) | oa⁆ * ⁅= x | oa'⁆ :=
begin
  rw [prob_output_seq_eq_tsum_indicator, ennreal.tsum_comm],
  simp_rw [set.indicator],
  simp only [eval_dist_apply_eq_prob_output, mul_ite, mul_zero, prob_event_eq_eq_prob_output_map],
  refine tsum_congr (λ x, _),
  by_cases hx : ∃ y, y * x = z,
  { obtain ⟨y, hy⟩ := hx,
    refine trans (tsum_eq_single (λ x, y * x) _) _,
    { simp only [ne.def, ite_eq_right_iff, mul_eq_zero, prob_output_eq_zero_iff,
        support_map, set.mem_image, not_exists, not_and],
      refine λ g hg hgx, or.inl (λ x' hx' hgx', hg (hgx'.symm.trans (congr_arg (*) _))),
      rw [set.mem_preimage, set.mem_singleton_iff, eq_comm] at hgx,
      rwa [hgx, ← hgx', mul_left_inj, eq_comm] at hy },
    { have : x ∈ has_mul.mul y ⁻¹' {z} := hy,
      simp only [this, eq_self_iff_true, if_true, prob_output_map_mul_right],
      by_cases hx : ⁅= x | oa'⁆ = 0,
      { by simp_rw [hx, mul_zero] },
        rw [ennreal.mul_eq_mul_right hx (prob_output_ne_top _ _)],
        refine symm (prob_output_map_eq_single _ _ _),
        simp [set.eq_singleton_iff_unique_mem, hy],
        refine λ y' hy', _,
        refine (mul_left_inj x).1 (hy'.trans hy.symm) } },
  { rw [not_exists] at hx,
    refine trans (ennreal.tsum_eq_zero.2 (λ g, _)) _,
    { split_ifs with h,
      { refine mul_eq_zero.2 (or.inl _),
        simp_rw [prob_output_eq_zero_iff, support_map, set.mem_image, not_exists, not_and_distrib],
        refine (λ y, (or.inr (λ h', hx y (trans (congr_fun h' x) h)))) },
      { refl }, },
    { rw [eq_comm, mul_eq_zero, prob_output_map_eq_tsum_indicator],
      refine or.inl (ennreal.tsum_eq_zero.2 (λ y,
        set.indicator_apply_eq_zero.2 (λ h, false.elim (hx y h)))) } }
end

/-- Given two computations `oa` and `oa'`, if there are unique outputs of each such that their
product is equal to `z`, then the probability of getting `z` from the sum of running both
computations can be written as a product of probabilities of getting each of them.-/
@[to_additive] lemma prob_output_seq_map_mul_cancel_unique [is_right_cancel_mul α] (z x y : α)
  (h : x * y = z) (h' : ∀ x' ∈ oa.support, ∀ y' ∈ oa'.support, x' * y' = z → y' = y) :
  ⁅= z | (*) <$> oa <*> oa'⁆ = ⁅= x | oa⁆ * ⁅= y | oa'⁆ :=
begin
  rw [prob_output_seq_map_mul],
  refine trans (tsum_eq_single y (λ y' hy', _)) _,
  { by_cases hy2 : y' ∈ oa'.support,
    { refine mul_eq_zero.2 (or.inl _),
      simp only [prob_event_eq_eq_prob_output_map, prob_output_eq_zero_iff,
        support_map, set.mem_image, not_exists, not_and],
      refine (λ x' hx hxy, hy' (h' x' hx y' hy2 hxy)) },
    { rw [prob_output_eq_zero hy2, mul_zero] } },
  { by_cases hyoa : y ∈ oa'.support,
    { refine congr_arg (λ z, z * ⁅= y | oa'⁆) _,
      refine prob_event_eq_prob_output x h (λ x' hx hx', _),
      refine (mul_left_inj y).1 (hx'.trans h.symm) },
    { rw [prob_output_eq_zero hyoa, mul_zero, mul_zero] } }
end

end is_cancel

section group

@[simp, to_additive] lemma prob_output_map_mul_right_eq_prob_output_div [group α] (x z : α) :
  ⁅= z | (* x) <$> oa⁆ = ⁅= z * x⁻¹ | oa⁆ :=
begin
  refine (prob_output_map_eq_single' oa (z * x⁻¹) _ (λ y hy hy', _)),
  { rw [inv_mul_cancel_right] },
  { rw [← hy', mul_inv_cancel_right] }
end

@[simp, to_additive] lemma prob_output_map_mul_left_eq_prob_output_div [group α] (x z : α) :
  ⁅= z | ((*) x) <$> oa⁆ = ⁅= x⁻¹ * z | oa⁆ :=
begin
  refine (prob_output_map_eq_single' oa (x⁻¹ * z) _ (λ y hy hy', _)),
  { rw [mul_inv_cancel_left] },
  { rw [← hy', ← mul_assoc, mul_left_inv, one_mul] }
end

end group

end oracle_comp