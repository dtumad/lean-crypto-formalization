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

namespace distribution_semantics

open oracle_spec oracle_comp ennreal nnreal 

variables {α β γ δ : Type} {spec spec' : oracle_spec} [finite_range spec] [finite_range spec']

section eval_dist

/-- Binding on a computation of a `prod` type can be written as a double sum,
instead of a sum of the product type. -/
lemma eval_dist_prod_bind (oa : oracle_comp spec (α × β)) (ob : α × β → oracle_comp spec γ)
  (c : γ) : ⦃oa >>= ob⦄ c = ∑' (a : α) (b : β), ⦃oa⦄ (a, b) * ⦃ob (a, b)⦄ c :=
by rw [eval_dist_bind, pmf.prod_bind_apply]

/-- Version of `eval_dist_prod_bind` with summation arguments swapped. -/
lemma eval_dist_prod_bind' (oa : oracle_comp spec (α × β)) (ob : α × β → oracle_comp spec γ)
  (c : γ) : ⦃oa >>= ob⦄ c = ∑' (b : β) (a : α), ⦃oa⦄ (a, b) * ⦃ob (a, b)⦄ c :=
by rw [eval_dist_bind, pmf.prod_bind_apply']

/-- The first output of a computation of a `prod` type is a sum over possible second outputs. -/
lemma eval_dist_map_fst (oa : oracle_comp spec (α × β)) (a : α) :
  ⦃prod.fst <$> oa⦄ a = ∑' (b : β), ⦃oa⦄ (a, b) :=
by rw [eval_dist_map, pmf.map_fst_apply]

/-- The second output of a computation of a `prod` type is a sum over possible first outputs -/
lemma eval_dist_map_snd (oa : oracle_comp spec (α × β)) (b : β) :
  ⦃prod.snd <$> oa⦄ b = ∑' (a : α), ⦃oa⦄ (a, b) :=
by rw [eval_dist_map, pmf.map_snd_apply]

end eval_dist

section prob_event

lemma prob_event_diagonal [hα : decidable_eq α] (oa : oracle_comp spec (α × α)) :
  ⦃set.diagonal α | oa⦄ = ∑' (a : α), ⦃oa⦄ (a, a) :=
calc ⦃set.diagonal α | oa⦄ = ∑' (x : α × α), ite (x ∈ set.diagonal α) (⦃oa⦄ x) 0 :
    prob_event_eq_tsum oa (set.diagonal α)
  ... = ∑' (a a' : α), ite (a = a') (⦃oa⦄ (a, a')) 0 :
    begin
      refine tsum_prod' _ _,
      { refine nnreal.summable_of_le (λ x, _) ⦃oa⦄.summable_coe,
        split_ifs; simp only [le_rfl, zero_le'] },
      { have : summable (λ a, ⦃oa⦄ (a, a)),
        from nnreal.summable_comp_injective ⦃oa⦄.summable_coe
          (λ x y hxy, (prod.eq_iff_fst_eq_snd_eq.1 hxy).1),
        refine λ a, nnreal.summable_of_le (λ a', _) this,
        split_ifs,
        { simp only [set.mem_diagonal_iff] at h,
          exact h ▸ le_rfl },
        { exact zero_le' } }
    end
  ... = ∑' (a a' : α), ite (a = a') (⦃oa⦄ (a, a)) 0 :
    tsum_congr (λ a, tsum_congr (λ a', by by_cases h : a = a'; simp only [h, if_false]))
  ... = ∑' (a a' : α), ite (a' = a) (⦃oa⦄ (a, a)) 0 : by simp_rw [@eq_comm]
  ... = ∑' (a : α), ⦃oa⦄ (a, a) : tsum_congr (λ a, tsum_ite_eq _ _) 

end prob_event

end distribution_semantics