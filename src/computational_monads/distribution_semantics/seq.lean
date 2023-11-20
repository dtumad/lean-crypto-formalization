/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.push_map_dist_equiv

/-!
# Distribution Semantics of Sequence Operation

This file contains lemmas about the distribution semantics of `<*>`, which can be use
to combine two computations with some operation.
For example given `oa ob : oracle_comp spec ℕ`, `(+) <$> oa <*> ob` is the computation that
runs `oa` and `ob` independently to get `x` and `y`, returning the sum `x + y`.
-/

namespace oracle_comp

open oracle_spec
open_locale ennreal big_operators

variables {α β γ δ : Type} {spec spec' : oracle_spec}
  (og : oracle_comp spec (α → β)) (oa oa' : oracle_comp spec α)

protected lemma seq_eq_bind_map : (og <*> oa) = (og >>= λ g, g <$> oa) := refl _

lemma seq_dist_equiv_bind_map : (og <*> oa) ≃ₚ (og >>= λ g, g <$> oa) := refl _

@[simp] lemma support_seq : (og <*> oa).support = ⋃ g ∈ og.support, g '' oa.support :=
by simp only [oracle_comp.seq_eq_bind_map, support_bind, support_map]

@[simp] lemma fin_support_seq [decidable_eq α] [decidable_eq (α → β)] [decidable_eq β] :
  (og <*> oa).fin_support = og.fin_support.bUnion (λ g, oa.fin_support.image g) :=
by simp [fin_support_eq_iff_support_eq_coe, mem_fin_support_iff_mem_support]

@[simp] lemma eval_dist_seq : ⁅og <*> oa⁆ = ⁅og⁆.bind (λ g, ⁅oa⁆.map g) :=
by simp [oracle_comp.seq_eq_bind_map]

@[simp] lemma prob_output_seq_eq_tsum [decidable_eq β] (y : β) :
  ⁅= y | og <*> oa⁆ = ∑' (g : α → β) x, if y = g x then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
by simp only [oracle_comp.seq_eq_bind_map, prob_output_bind_eq_tsum, prob_output_map_eq_tsum,
  ← ennreal.tsum_mul_left, eval_dist_apply_eq_prob_output, mul_ite, mul_zero]

lemma prob_output_seq_eq_tsum_indicator (y : β) :
  ⁅= y | og <*> oa⁆ = ∑' (g : α → β) x, ⁅= g | og⁆ * (g ⁻¹' {y}).indicator ⁅oa⁆ x :=
by simp only [oracle_comp.seq_eq_bind_map, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left,
  prob_output_map_eq_tsum_indicator]

@[simp] lemma prob_event_seq (e : set β) : ⁅e | og <*> oa⁆ = ∑' g, ⁅= g | og⁆ * ⁅g ⁻¹' e | oa⁆ :=
by simp [oracle_comp.seq_eq_bind_map, prob_event_bind_eq_tsum]

@[simp] lemma prob_event_seq_eq_tsum_ite (e : set β) [decidable_pred (∈ e)] :
  ⁅e | og <*> oa⁆ = ∑' (g : α → β) x, if g x ∈ e then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
by simp only [oracle_comp.seq_eq_bind_map, prob_event_bind_eq_tsum, prob_event_map_eq_tsum,
  ← ennreal.tsum_mul_left, eval_dist_apply_eq_prob_output, mul_ite, mul_zero]

section comm

lemma seq_map_dist_equiv_comm (f : α → α → β) (hf : ∀ x x', f x x' = f x' x) :
  f <$> oa <*> oa' ≃ₚ f <$> oa' <*> oa :=
begin
  rw_dist_equiv [seq_dist_equiv_bind_map, seq_dist_equiv_bind_map, bind_map_dist_equiv,
    bind_map_dist_equiv, map_dist_equiv_bind_return, bind_bind_dist_equiv_comm],
  pairwise_dist_equiv_deep,
  refine return_dist_equiv_return_of_eq _ _ _ _ (hf _ _)
end

@[pairwise_dist_equiv] lemma seq_map_mul_dist_equiv_comm [comm_monoid α] :
  (*) <$> oa <*> oa' ≃ₚ (*) <$> oa' <*> oa := seq_map_dist_equiv_comm oa oa' (*) mul_comm

@[pairwise_dist_equiv] lemma seq_map_add_dist_equiv_comm [add_comm_monoid α] :
  (+) <$> oa <*> oa' ≃ₚ (+) <$> oa' <*> oa := seq_map_dist_equiv_comm oa oa' (+) add_comm

end comm

section cancel

/-- In an `cancel_monoid`, the output of multiplying the result of two computations has probability
given by summing over the probabilities of each possible result of the first computation. -/
lemma prob_output_seq_map_mul_cancel [decidable_eq α] [cancel_monoid α] (z : α) :
  ⁅= z | (*) <$> oa <*> oa'⁆ = ∑' x, ⁅(= z) ∘ (* x) | oa⁆ * ⁅= x | oa'⁆ :=
begin
  -- haveI : decidable_eq α := classical.dec_eq α,
  rw [prob_output_seq_eq_tsum, ennreal.tsum_comm],
  refine tsum_congr (λ x, _),
  by_cases hx : ∃ y, y * x = z,
  { obtain ⟨y, hy⟩ := hx,
    refine trans (tsum_eq_single (λ x, y * x) _) _,
    { simp only [ne.def, ite_eq_right_iff, mul_eq_zero, prob_output_eq_zero_iff,
        support_map, set.mem_image, not_exists, not_and],
      refine λ g hg hgx, or.inl (λ x' hx' hgx', hg (hgx'.symm.trans (congr_arg (*) _))),
      rwa [hgx, ← hgx', mul_left_inj, eq_comm] at hy },
    { simp only [hy, eq_self_iff_true, if_true],
      rw [prob_output_map_mul_right, prob_event_eq_prob_output _ y hy],
      exact λ y' hy' hyy', (hy' (symm ((mul_left_inj x).1 (hy.trans hyy'.symm)))).elim } },
  { rw [not_exists] at hx,
    refine trans (ennreal.tsum_eq_zero.2 (λ g, _)) _,
    { refine ite_eq_right_iff.2 (λ hz, mul_eq_zero.2 (or.inl _)),
      simp_rw [prob_output_eq_zero_iff, support_map, set.mem_image, not_exists, not_and_distrib],
      exact λ y, or.inr (λ hg, hx y ((congr_fun hg x).trans hz.symm)) },
    { rw [eq_comm, mul_eq_zero, ← prob_event_map', prob_event_eq_eq_prob_output',
        prob_output_map_eq_tsum],
      exact or.inl (ennreal.tsum_eq_zero.2 (λ y, if_neg (ne.symm (hx y)))) } }
end

/-- In an `add_cancel_monoid`, the output of adding the result of two computations has probability
given by summing over the probabilities of each possible result of the first computation. -/
lemma prob_output_seq_map_add_cancel [decidable_eq α] [add_cancel_monoid α] (z : α) :
  ⁅= z | (+) <$> oa <*> oa'⁆ = ∑' x₀, ⁅(= z) ∘ (+ x₀) | oa⁆ * ⁅= x₀ | oa'⁆ :=
begin
  -- haveI : decidable_eq α := classical.dec_eq α,
  rw [prob_output_seq_eq_tsum, ennreal.tsum_comm],
  refine tsum_congr (λ x, _),
  by_cases hx : ∃ y, y + x = z,
  { obtain ⟨y, hy⟩ := hx,
    refine trans (tsum_eq_single (λ x, y + x) _) _,
    { simp only [ne.def, ite_eq_right_iff, mul_eq_zero, prob_output_eq_zero_iff,
        support_map, set.mem_image, not_exists, not_and],
      refine λ g hg hgx, or.inl (λ x' hx' hgx', hg (hgx'.symm.trans (congr_arg (+) _))),
      rwa [hgx, ← hgx', add_left_inj, eq_comm] at hy },
    { simp only [hy, eq_self_iff_true, if_true],
      rw [prob_output_map_add_right, prob_event_eq_prob_output _ y hy],
      exact λ y' hy' hyy', (hy' (symm ((add_left_inj x).1 (hy.trans hyy'.symm)))).elim } },
  { rw [not_exists] at hx,
    refine trans (ennreal.tsum_eq_zero.2 (λ g, _)) _,
    { refine ite_eq_right_iff.2 (λ hz, mul_eq_zero.2 (or.inl _)),
      simp_rw [prob_output_eq_zero_iff, support_map, set.mem_image, not_exists, not_and_distrib],
      exact λ y, or.inr (λ hg, hx y ((congr_fun hg x).trans hz.symm)) },
    { rw [eq_comm, mul_eq_zero, ← prob_event_map', prob_event_eq_eq_prob_output',
        prob_output_map_eq_tsum],
      exact or.inl (ennreal.tsum_eq_zero.2 (λ y, if_neg (ne.symm (hx y)))) } }
end

/-- Given two computations `oa` and `oa'`, if there are unique outputs of each such that their
sum is equval to `z`, then the probability of getting `z` from the sum of running both computations
can be written as a product of probabilities of getting each of them.-/
lemma prob_output_seq_map_add_cancel_unique [decidable_eq α] [has_add α] [is_right_cancel_add α]
  (z : α) (x y : α) (h : x + y = z)
  (h' : ∀ x' ∈ oa.support, ∀ y' ∈ oa'.support, x' + y' = z → x' = x ∧ y' = y) :
  ⁅= z | (+) <$> oa <*> oa'⁆ = ⁅= x | oa⁆ * ⁅= y | oa'⁆ :=
begin
  rw [prob_output_seq_eq_tsum, ← ennreal.tsum_prod],
  refine trans (tsum_eq_single (((+) x, y)) _) _,
  {
    rintros ⟨g, y'⟩ hg,
    refine ite_eq_right_iff.2 (λ hz, _),
    replace hz : z = g y' := hz,
    simp only at ⊢,
    by_contra hgy,
    simp_rw [mul_eq_zero, not_or_distrib, prob_output_eq_zero_iff, not_not, support_map] at hgy,
    obtain ⟨x', hx'⟩ := hgy.1,
    have := trans (congr_fun hx'.2 y') hz.symm,

    specialize h' x' hx'.1 y' hgy.2 this,
    refine hg _,
    refine prod.eq_iff_fst_eq_snd_eq.2 ⟨hx'.2.symm.trans _, h'.2⟩,
    rw [h'.1],
  },
  {
    simp only [h, eq_self_iff_true, prob_output_map_add_right, if_true],
  }
end

end cancel

end oracle_comp