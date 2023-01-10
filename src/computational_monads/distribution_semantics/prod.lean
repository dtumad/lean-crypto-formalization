/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.prob_event

/-!
# Probabilities for Computations Over Prod Type

General lemmas about probability computations involving `prod`
-/

namespace oracle_comp

open oracle_spec distribution_semantics
open_locale big_operators ennreal


variables {α β γ δ : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec (α × β)) (oc : α × β → oracle_comp spec γ)

section eval_dist

/-- Binding on a computation of a `prod` type can be written as a double sum,
instead of a sum of the product type. -/
lemma eval_dist_prod_bind (c : γ) :
  ⁅oa >>= oc⁆ c = ∑' (a : α) (b : β), ⁅oa⁆ (a, b) * ⁅oc (a, b)⁆ c :=
by rw [eval_dist_bind_apply_eq_tsum, ennreal.tsum_prod']

/-- Version of `eval_dist_prod_bind` with summation arguments swapped. -/
lemma eval_dist_prod_bind' (c : γ) :
  ⁅oa >>= oc⁆ c = ∑' (b : β) (a : α), ⁅oa⁆ (a, b) * ⁅oc (a, b)⁆ c :=
by rw [eval_dist_bind_apply_eq_tsum, ennreal.tsum_prod', ennreal.tsum_comm]

/-- The first output of a computation of a `prod` type is a sum over possible second outputs. -/
lemma eval_dist_map_fst (a : α) : ⁅prod.fst <$> oa⁆ a = ∑' (b : β), ⁅oa⁆ (a, b) :=
by rw [eval_dist_map, pmf.map_fst_apply]

/-- The second output of a computation of a `prod` type is a sum over possible first outputs -/
lemma eval_dist_map_snd (b : β) : ⁅prod.snd <$> oa⁆ b = ∑' (a : α), ⁅oa⁆ (a, b) :=
by rw [eval_dist_map, pmf.map_snd_apply]

/-- If only the left output is changed in mapping the result of a computation,
then the resulting distribution sums only over the left type in the product type. -/
lemma eval_dist_map_prod_map_id_right_apply [decidable_eq β] [decidable_eq γ] (f : α → γ)
  (z : γ × β) : ⁅prod.map f id <$> oa⁆ z = ∑' (x : α), ite (z.1 = f x) (⁅oa⁆ (x, z.2)) 0 :=
begin
  rw [eval_dist_map_apply_eq_tsum, ennreal.tsum_prod'],
  refine tsum_congr (λ x, (tsum_eq_single z.2 _).trans _),
  { exact λ y hy, if_neg $ by simp only [prod.eq_iff_fst_eq_snd_eq, hy.symm,
      prod.map_mk, id.def, and_false, not_false_iff] },
  { simp only [prod.eq_iff_fst_eq_snd_eq, prod.map_mk, id.def, eq_self_iff_true, and_true] },
end

/-- If only the right output is changed in mapping the result of a computation,
then the resulting distribution sums only over the right type in the product type. -/
lemma eval_dist_map_prod_map_id_left_apply [decidable_eq α] [decidable_eq γ] (f : β → γ)
  (z : α × γ) : ⁅prod.map id f <$> oa⁆ z = ∑' (y : β), ite (z.2 = f y) (⁅oa⁆ (z.1, y)) 0 :=
begin
  rw [eval_dist_map_apply_eq_tsum, ennreal.tsum_prod', ennreal.tsum_comm],
  refine tsum_congr (λ x, (tsum_eq_single z.1 _).trans _),
  { exact λ y hy, if_neg $ by simp only [prod.eq_iff_fst_eq_snd_eq, hy.symm,
      prod.map_mk, id.def, false_and, not_false_iff]},
  { simp only [prod.eq_iff_fst_eq_snd_eq, prod.map_mk, id.def, eq_self_iff_true, true_and] },
end

end eval_dist

section prob_event

lemma prob_event_diagonal [decidable_eq α] (oa : oracle_comp spec (α × α)) :
  ⁅set.diagonal α | oa⁆ = ∑' (a : α), ⁅oa⁆ (a, a) :=
calc ⁅set.diagonal α | oa⁆ = ∑' (x : α × α), ite (x ∈ set.diagonal α) (⁅oa⁆ x) 0 :
    prob_event_eq_tsum_ite oa (set.diagonal α)
  ... = ∑' (a a' : α), ite (a = a') (⁅oa⁆ (a, a')) 0 :
    tsum_prod' ennreal.summable (λ _, ennreal.summable)
  ... = ∑' (a a' : α), ite (a = a') (⁅oa⁆ (a, a)) 0 :
    tsum_congr (λ a, tsum_congr (λ a', by by_cases h : a = a'; simp only [h, if_false]))
  ... = ∑' (a a' : α), ite (a' = a) (⁅oa⁆ (a, a)) 0 : by simp_rw [@eq_comm]
  ... = ∑' (a : α), ⁅oa⁆ (a, a) : tsum_congr (λ a, tsum_ite_eq _ _)

end prob_event

end oracle_comp