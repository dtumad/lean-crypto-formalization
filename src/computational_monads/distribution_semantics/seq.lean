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

@[simp] lemma fin_support_seq [decidable_eq β] : (og <*> oa).fin_support =
  og.fin_support.bUnion (λ g, oa.fin_support.image g) :=
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

@[pairwise_dist_equiv]
lemma seq_map_mul_dist_equiv_comm [comm_monoid α] : (*) <$> oa <*> oa' ≃ₚ (*) <$> oa' <*> oa :=
seq_map_dist_equiv_comm oa oa' (*) mul_comm

@[pairwise_dist_equiv]
lemma seq_map_add_dist_equiv_comm [add_comm_monoid α] : (+) <$> oa <*> oa' ≃ₚ (+) <$> oa' <*> oa :=
seq_map_dist_equiv_comm oa oa' (+) add_comm

end comm

section cancel

lemma seq_map_add_dist_equiv_cancel [add_cancel_monoid α] (z : α) :
  ⁅= z | (+) <$> oa <*> oa'⁆ = ∑' x, ⁅λ y, y + x = z | oa⁆ * ⁅= x | oa'⁆ :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  rw [prob_output_seq_eq_tsum, ennreal.tsum_comm],
  refine tsum_congr (λ x, _),
  by_cases hx : ∃ y, y + x = z,
  {
    obtain ⟨y, hy⟩ := hx,
    refine trans (tsum_eq_single (λ x, y + x) _) _,
    {
      simp only [ne.def, ite_eq_right_iff, mul_eq_zero, prob_output_eq_zero_iff, support_map, set.mem_image, not_exists, not_and],
      intros g hg hgx,
      refine or.inl (λ x' hx' hgx', hg (hgx'.symm.trans _)),
      rw [hgx, ← hgx', add_left_inj] at hy,
      simp [hy],
    },
    {
      simp [hy],
      sorry,
    }
  },
  {
    sorry,
  }
end

end cancel

end oracle_comp