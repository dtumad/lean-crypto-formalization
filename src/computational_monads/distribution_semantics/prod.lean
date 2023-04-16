/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad

/-!
# Probabilities for Computations Over Prod Type

General lemmas about probability computations involving `prod`
-/

namespace oracle_comp

open oracle_spec
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


namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec} (oa : oracle_comp spec α)
  (f : α → β) (g : α → γ) (b : β) (c : γ)

section bind_prod_mk

section support

lemma support_bind_prod_mk : (oa >>= λ a, return (f a, g a)).support =
  (λ a, (f a, g a)) '' oa.support := support_bind_return oa _

lemma support_map_prod_mk : ((λ a, (f a, g a) : α → β × γ) <$> oa).support =
  (λ a, (f a, g a)) '' oa.support := support_map oa _

lemma mem_support_bind_prod_mk (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ y ∈ oa.support, f y = x.1 ∧ g y = x.2 :=
by simp only [support_bind_return, set.mem_image, exists_prop, prod.eq_iff_fst_eq_snd_eq]

lemma mem_support_map_prod_mk (x : β × γ) :
  x ∈ ((λ a, (f a, g a) : α → β × γ) <$> oa).support ↔ ∃ y ∈ oa.support, f y = x.1 ∧ g y = x.2 :=
mem_support_bind_prod_mk oa f g x

lemma mem_support_bind_prod_mk_id_fst (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, g a)).support ↔ x.1 ∈ oa.support ∧ g x.1 = x.2 :=
calc x ∈ (oa >>= λ a, return (a, g a)).support
  ↔ ∃ y, y ∈ oa.support ∧ y = x.1 ∧ g y = x.2 : by simp_rw [mem_support_bind_prod_mk, exists_prop]
  ... ↔ ∃ y, y = x.1 ∧ y ∈ oa.support ∧ g y = x.2 :
    exists_congr (λ y, by simp_rw [and_comm (y ∈ oa.support), and_assoc])
  ... ↔ x.1 ∈ oa.support ∧ g x.1 = x.2 : exists_eq_left

lemma mem_support_bind_prod_mk_id_snd (x : β × α) :
  x ∈ (oa >>= λ a, return (f a, a)).support ↔ x.2 ∈ oa.support ∧ f x.2 = x.1  :=
calc x ∈ (oa >>= λ a, return (f a, a)).support
  ↔ ∃ y, y ∈ oa.support ∧ f y = x.1 ∧ y = x.2 : by simp_rw [mem_support_bind_prod_mk, exists_prop]
  ... ↔ x.2 ∈ oa.support ∧ f x.2 = x.1 : by rw [exists_eq_right_right]

lemma mem_support_bind_prod_mk_fst (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).support ↔ x.1 ∈ f '' oa.support ∧ x.2 = c :=
by simp_rw [support_bind_prod_mk, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_right, and_assoc, @eq_comm γ c]

lemma mem_support_bind_prod_mk_snd (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, g a)).support ↔ x.1 = b ∧ x.2 ∈ g '' oa.support :=
by simp_rw [support_bind_prod_mk, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_left, @eq_comm β b, ← and_assoc, and_comm (x.1 = b)]

end support

section fin_support

variables [decidable oa]

lemma fin_support_bind_prod_mk [decidable_eq β] [decidable_eq γ] :
  (oa >>= λ a, return (f a, g a)).fin_support = oa.fin_support.image (λ a, (f a, g a)) :=
fin_support_bind_return oa _

lemma mem_fin_support_bind_prod_mk [decidable_eq β] [decidable_eq γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).fin_support ↔ ∃ y ∈ oa.fin_support, f y = x.1 ∧ g y = x.2 :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk]

lemma mem_fin_support_bind_prod_mk_id_fst [decidable_eq α] [decidable_eq γ] (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, g a)).fin_support ↔ x.1 ∈ oa.fin_support ∧ g x.1 = x.2 :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_id_fst]

lemma mem_fin_support_bind_prod_mk_id_snd [decidable_eq α] [decidable_eq β] (x : β × α) :
  x ∈ (oa >>= λ a, return (f a, a)).fin_support ↔ x.2 ∈ oa.fin_support ∧ f x.2 = x.1  :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_id_snd]

lemma mem_fin_support_bind_prod_mk_fst [decidable_eq β] [decidable_eq γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).fin_support ↔ x.1 ∈ oa.fin_support.image f ∧ x.2 = c :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_fst,
  set.mem_image, finset.mem_image, exists_prop]

lemma mem_fin_support_bind_prod_mk_snd [decidable_eq β] [decidable_eq γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, g a)).fin_support ↔ x.1 = b ∧ x.2 ∈ oa.fin_support.image g :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_snd,
  set.mem_image, finset.mem_image, exists_prop]

end fin_support

end bind_prod_mk

section bind_prod_mk_subsingleton

section support

@[simp] lemma support_bind_prod_mk_of_fst_subsingleton [subsingleton β] :
  (oa >>= λ a, return (f a, g a)).support = prod.snd ⁻¹' (g '' oa.support) :=
set.ext (λ x, by simp only [support_bind_prod_mk, set.mem_image, set.mem_preimage,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, true_and])

@[simp] lemma support_bind_prod_mk_of_snd_subsingleton [subsingleton γ] :
  (oa >>= λ a, return (f a, g a)).support = prod.fst ⁻¹' (f '' oa.support) :=
set.ext (λ x, by simp only [support_bind_prod_mk, set.mem_image, set.mem_preimage,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, and_true])

lemma mem_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, f a = x.1 :=
by simp_rw [support_bind_prod_mk_of_snd_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

lemma mem_support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, g a = x.2 :=
by simp_rw [support_bind_prod_mk_of_fst_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

end support

section fin_support

variables [decidable oa]

@[simp] lemma fin_support_bind_prod_mk_fst_of_subsingleton [decidable_eq β] [subsingleton γ] :
  (oa >>= λ a, return (f a, g a)).fin_support = (oa.fin_support.image f).preimage prod.fst
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨h, subsingleton.elim _ _⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk, finset.mem_preimage, finset.mem_image,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, and_true])

@[simp] lemma fin_support_bind_prod_mk_snd_of_subsingleton [decidable_eq γ] [subsingleton β] :
  (oa >>= λ a, return (f a, g a)).fin_support = (oa.fin_support.image g).preimage prod.snd
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨subsingleton.elim _ _, h⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk, finset.mem_preimage, finset.mem_image,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, true_and])

lemma mem_fin_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, f a = x.1 :=
by simp_rw [support_bind_prod_mk_of_snd_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

lemma mem_fin_support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, g a = x.2 :=
by simp_rw [support_bind_prod_mk_of_fst_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

end fin_support

end bind_prod_mk_subsingleton

section map_fst_snd

section support

lemma mem_support_map_fst_iff (oab : oracle_comp spec (α × β)) (x : α) :
  x ∈ (prod.fst <$> oab).support ↔ ∃ y, (x, y) ∈ oab.support :=
by simp only [support_map, set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right]

lemma mem_support_map_snd_iff (oab : oracle_comp spec (α × β)) (y : β) :
  y ∈ (prod.snd <$> oab).support ↔ ∃ x, (x, y) ∈ oab.support :=
by simp only [support_map, set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right]

end support

section fin_support

end fin_support

end map_fst_snd

end oracle_comp