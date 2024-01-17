/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.push_map_dist_equiv
import computational_monads.distribution_semantics.mprod

/-!
# Probabilities for Computations Over Prod Type

General lemmas about probability computations involving `prod`

TODO: orginization/naming in this file has bad vibes.
-/

namespace oracle_comp

open oracle_spec prod
open_locale big_operators ennreal

variables {α β γ δ : Type} {spec spec' : oracle_spec}

-- lemma prob_output_prod_eq_mul (oc : oracle_comp spec (α × β))
--   (z : α × β)
--   (h : ∀ x y y', ⁅= (x, y) | oc⁆ = ⁅= (x, y') | oc⁆)
--   (h' : ∀ x x' y, ⁅= (x, y) | oc⁆ = ⁅= (x', y) | oc⁆) :
--   ⁅= z | oc⁆ = ⁅= z.1 | fst <$> oc⁆ * ⁅= z.2 | snd <$> oc⁆ :=
-- begin
--   rw [← prob_event_eq_eq_prob_output],
--   rw [prob_event_eq_of_iff oc (λ z, @prod.eq_iff_fst_eq_snd_eq _ _ _ z)],
--   rw [prob_event_map_bind],
--   simp_rw [prod.eq_iff_fst_eq_snd_eq],
-- end

@[simp] lemma prob_output_prod_return (z z' : α × β) :
  ⁅= z | (return z' : oracle_comp spec (α × β))⁆ =
    ⁅= z.1 | (return z'.1 : oracle_comp spec α)⁆ *
      ⁅= z.2 | (return z'.2 : oracle_comp spec β)⁆ :=
begin
  by_cases hz : z = z',
  { simp only [hz, prob_output_return_self, mul_one] },
  { simpa only [prob_output_return_of_ne _ hz, zero_eq_mul,
      prob_output_return_eq_zero_iff, eq_iff_fst_eq_snd_eq, not_and_distrib] using hz }
end

lemma prob_output_return_prod_mk_fst (x x' : α) (y : β) :
  ⁅= (x, y) | return' !spec! (x', y)⁆ = ⁅= x | return' !spec! x'⁆ :=
by simp

lemma prob_output_return_prod_mk_snd (x : α) (y y' : β) :
  ⁅= (x, y) | return' !spec! (x, y')⁆ = ⁅= y | return' !spec! y'⁆ :=
by simp

section fst_snd_map_return_dist_equiv

-- lemma fst_map_return_dist_equiv (x : α) (y : β) :
--   fst <$> (return' !spec! (x, y)) ≃ₚ return' !spec! x :=
-- by pairwise_dist_equiv

-- lemma fst_map_return_dist_equiv' (x : α) (y : β) (f : α → γ) :
--   (λ (x : α × β), f x.1) <$> (return' !spec! (x, y)) ≃ₚ return' !spec! (f x) :=
-- by pairwise_dist_equiv

-- lemma snd_map_return_dist_equiv (x : α) (y : β) :
--   snd <$> (return' !spec! (x, y)) ≃ₚ return' !spec! y :=
-- by pairwise_dist_equiv

-- lemma snd_map_return_dist_equiv' (x : α) (y : β) (f : β → γ) :
--   (λ (x : α × β), f x.2) <$> (return' !spec! (x, y)) ≃ₚ return' !spec! (f y) :=
-- by pairwise_dist_equiv

-- @[pairwise_dist_equiv] lemma fst_map_return_dist_equiv_fst_map_return (x : α) (y y' : β) :
--   fst <$> (return' !spec! (x, y)) ≃ₚ fst <$> (return' !spec! (x, y')) :=
-- by simp_rw_dist_equiv [map_return_dist_equiv]

-- @[pairwise_dist_equiv] lemma snd_map_return_dist_equiv_snd_map_return (x x' : α) (y : β) :
--   snd <$> (return' !spec! (x, y)) ≃ₚ snd <$> (return' !spec! (x', y)) :=
-- by simp_rw_dist_equiv [map_return_dist_equiv]

end fst_snd_map_return_dist_equiv

section fst_snd_map_bind_return_dist_equiv

variables (oa : oracle_comp spec α) (f : α → β) (g : α → γ) (h : α → δ)

/-- Without making this a simp lemma it will reduce to `do {x ← oa, return (f x)}`. -/
@[simp] lemma fst_map_bind_return :
  (fst <$> (do {x ← oa, return (f x, g x)}) : oracle_comp spec β) = f <$> oa :=
by simpa only [map_bind]

/-- Without making this a simp lemma it will reduce to `do {x ← oa, return (g x)}`. -/
@[simp] lemma snd_map_bind_return :
  (snd <$> (do {x ← oa, return (f x, g x)}) : oracle_comp spec γ) = g <$> oa :=
by simpa only [map_bind]

-- lemma fst_map_bind_return_dist_equiv :
--   fst <$> (oa >>= λ x, return (f x, g x)) ≃ₚ f <$> oa :=
-- by rw_dist_equiv [map_bind_dist_equiv]

-- lemma snd_map_bind_return_dist_equiv :
--   snd <$> (oa >>= λ x, return (f x, g x)) ≃ₚ g <$> oa :=
-- by rw [snd_map_bind_return]

end fst_snd_map_bind_return_dist_equiv

section unused

variables (oa : oracle_comp spec (α × β))

@[simp] lemma bind_eq_fst_bind_of_unused (oc : α → oracle_comp spec γ) :
  oa >>= (λ x, oc x.1) = (fst <$> oa) >>= oc :=
by simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

@[simp] lemma bind_eq_snd_bind_of_unused (oc' : β → oracle_comp spec γ) :
  oa >>= (λ x, oc' x.2) = (snd <$> oa) >>= oc' :=
by simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

@[pairwise_dist_equiv] lemma bind_dist_equiv_fst_bind_of_unused (oc : α → oracle_comp spec γ) :
  oa >>= (λ x, oc x.1) ≃ₚ (fst <$> oa) >>= oc :=
by rw_dist_equiv [bind_map_dist_equiv]

@[pairwise_dist_equiv] lemma bind_dist_equiv_snd_bind_of_unused (oc' : β → oracle_comp spec γ) :
  oa >>= (λ x, oc' x.2) ≃ₚ (snd <$> oa) >>= oc' :=
by rw_dist_equiv [bind_map_dist_equiv]

end unused

section prod_bind

variables (oa : oracle_comp spec (α × β)) (oc : α × β → oracle_comp spec γ)

/-- The probability on binding on a computation of a `prod` type can be written as a double sum,
by splitting the sum over the regular product type -/
lemma prob_output_prod_bind (c : γ) :
  ⁅= c | oa >>= oc⁆ = ∑' (a : α) (b : β), ⁅= (a, b) | oa⁆ * ⁅= c | oc (a, b)⁆ :=
by rw [prob_output_bind_eq_tsum, ennreal.tsum_prod']

/-- Version of `prob_output_prod_bind` with summation arguments swapped. -/
lemma prob_output_prod_bind' (c : γ) :
  ⁅= c | oa >>= oc⁆ = ∑' (b : β) (a : α), ⁅= (a, b) | oa⁆ * ⁅= c | oc (a, b)⁆ :=
by rw [prob_output_prod_bind, ennreal.tsum_comm]

lemma prob_event_prod_bind (e : set γ) :
  ⁅e | oa >>= oc⁆ = ∑' (a : α) (b : β), ⁅= (a, b) | oa⁆ * ⁅e | oc (a, b)⁆ :=
by rw [prob_event_bind_eq_tsum, ennreal.tsum_prod']

lemma prob_event_prod_bind' (e : set γ) :
  ⁅e | oa >>= oc⁆ = ∑' (b : β) (a : α), ⁅= (a, b) | oa⁆ * ⁅e | oc (a, b)⁆ :=
by rw [prob_event_prod_bind, ennreal.tsum_comm]

end prod_bind

section map_fst_snd

variables (oa : oracle_comp spec (α × β))

lemma mem_support_map_fst_iff (oab : oracle_comp spec (α × β)) (x : α) :
  x ∈ (fst <$> oab).support ↔ ∃ y, (x, y) ∈ oab.support :=
by simp only [support_map, set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right]

lemma mem_support_map_snd_iff (oab : oracle_comp spec (α × β)) (y : β) :
  y ∈ (snd <$> oab).support ↔ ∃ x, (x, y) ∈ oab.support :=
by simp only [support_map, set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right]

lemma mem_fin_support_map_fst_iff [decidable_eq α] (oab : oracle_comp spec (α × β)) (x : α) :
  x ∈ (fst <$> oab).fin_support ↔ ∃ y, (x, y) ∈ oab.support :=
by rw [mem_fin_support_iff_mem_support, mem_support_map_fst_iff]

lemma mem_fin_support_map_snd_iff [decidable_eq β] (oab : oracle_comp spec (α × β)) (y : β) :
  y ∈ (snd <$> oab).fin_support ↔ ∃ x, (x, y) ∈ oab.support :=
by rw [mem_fin_support_iff_mem_support, mem_support_map_snd_iff]

/-- The first output of a computation of a `prod` type is a sum over possible second outputs.
TODO: decide on `simp` conventions for lemmas like this one. -/
lemma prob_output_map_fst (a : α) : ⁅= a | fst <$> oa⁆ = ∑' (b : β), ⁅= (a, b) | oa⁆ :=
by simp only [prob_output.def, eval_dist_map, pmf.map_fst_apply]

lemma prob_output_map_fst' [decidable_eq β] (x : α) :
  ⁅= x | fst <$> oa⁆ = ∑ y in (snd <$> oa).fin_support, ⁅= (x, y) | oa⁆ :=
(prob_output_map_fst oa x).trans (tsum_eq_sum (λ y hy, prob_output_eq_zero
  (λ h, hy (mem_fin_support_of_mem_support (apply_mem_support_map h snd)))))

/-- The second output of a computation of a `prod` type is a sum over possible first outputs -/
lemma prob_output_map_snd (b : β) : ⁅= b | snd <$> oa⁆ = ∑' (a : α), ⁅= (a, b) | oa⁆ :=
by simp only [prob_output.def, eval_dist_map, pmf.map_snd_apply]

lemma prob_output_map_snd' [decidable_eq α] (y : β) :
  ⁅= y | snd <$> oa⁆ = ∑ x in (fst <$> oa).fin_support, ⁅= (x, y) | oa⁆ :=
(prob_output_map_snd oa y).trans (tsum_eq_sum (λ x hx, prob_output_eq_zero
  (λ h, hx (mem_fin_support_of_mem_support (apply_mem_support_map h fst)))))

end map_fst_snd

section prod_map_id

variables (oa : oracle_comp spec (α × β))

@[simp] lemma support_map_prod_map_id_right (f : α → γ) :
  (map f id <$> oa).support = {z | ∃ x, (x, z.2) ∈ oa.support ∧ f x = z.1} :=
begin
  simp only [set.ext_iff, set.image, eq_iff_fst_eq_snd_eq, support_map, prod_map, id.def,
    exists_eq_right_right,
    set.mem_set_of_eq, prod.exists, prod.forall],
  simp only [iff_self, forall_2_true_iff],
end

@[simp] lemma support_map_prod_map_id_left (g : β → γ) :
  (map id g <$> oa).support = {z | ∃ y, (z.1, y) ∈ oa.support ∧ g y = z.2} :=
begin
  refine set.ext (λ z, _),
  cases z with x y,
  simp [and_comm (_ = x), @exists_comm α],
end

/-- If only the left output is changed in mapping the result of a computation,
then the resulting distribution sums only over the left type in the product type. -/
lemma prob_output_map_prod_map_id_right [decidable_eq β] [decidable_eq γ] (f : α → γ)
  (z : γ × β) : ⁅= z | prod.map f id <$> oa⁆ = ∑' (x : α), ite (z.1 = f x) ⁅= (x, z.2) | oa⁆ 0 :=
begin
  rw [prob_output_map_eq_tsum, ennreal.tsum_prod'],
  refine tsum_congr (λ x, (tsum_eq_single z.2 _).trans _),
  { exact λ y hy, if_neg $ by simp only [eq_iff_fst_eq_snd_eq, hy.symm,
      prod.map_mk, id.def, and_false, not_false_iff] },
  { simp [eq_iff_fst_eq_snd_eq, prod.map_mk, id.def, eq_self_iff_true, and_true] },
end

/-- If only the right output is changed in mapping the result of a computation,
then the resulting distribution sums only over the right type in the product type. -/
lemma prob_output_map_prod_map_id_left [decidable_eq α] [decidable_eq γ] (f : β → γ)
  (z : α × γ) : ⁅= z | prod.map id f <$> oa⁆ = ∑' (y : β), ite (z.2 = f y) ⁅= (z.1, y) | oa⁆ 0 :=
begin
  rw [prob_output_map_eq_tsum, ennreal.tsum_prod', ennreal.tsum_comm],
  refine tsum_congr (λ x, (tsum_eq_single z.1 _).trans _),
  { exact λ y hy, if_neg $ by simp only [eq_iff_fst_eq_snd_eq, hy.symm,
      prod.map_mk, id.def, false_and, not_false_iff]},
  { simp only [eq_iff_fst_eq_snd_eq, prod.map_mk, id.def, eq_self_iff_true, true_and] },
end

end prod_map_id

section fst_snd_map_bind

variables (oa : oracle_comp spec (α × β))

lemma bind_dist_equiv_fst_bind (oc : α × β → oracle_comp spec γ) (y : β)
  (h : ∀ z, oc z ≃ₚ oc (z.1, y)) : oa >>= oc ≃ₚ (fst <$> oa >>= λ x, oc (x, y)) :=
begin
  rw_dist_equiv [bind_map_dist_equiv],
  refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, h x)
end

lemma bind_dist_equiv_snd_bind (oc : α × β → oracle_comp spec γ) (x : α)
  (h : ∀ z, oc z ≃ₚ oc (x, z.2)): oa >>= oc ≃ₚ (snd <$> oa >>= λ y, oc (x, y)) :=
begin
  rw_dist_equiv [bind_map_dist_equiv],
  refine bind_dist_equiv_bind_of_dist_equiv_right _ _ _ (λ x hx, h x)
end

end fst_snd_map_bind

section prob_event

@[simp] lemma prob_event_diagonal [decidable_eq α] (oa : oracle_comp spec (α × α)) :
  ⁅set.diagonal α | oa⁆ = ∑' a : α, ⁅= (a, a) | oa⁆ :=
calc ⁅set.diagonal α | oa⁆ = ∑' (x : α × α), ite (x ∈ set.diagonal α) ⁅= x | oa⁆ 0 :
    prob_event_eq_tsum_ite oa (set.diagonal α)
  ... = ∑' (a a' : α), ite (a = a') ⁅= (a, a') | oa⁆ 0 :
    tsum_prod' ennreal.summable (λ _, ennreal.summable)
  ... = ∑' (a a' : α), ite (a = a') ⁅= (a, a) | oa⁆ 0 :
    tsum_congr (λ a, tsum_congr (λ a', by by_cases h : a = a'; simp only [h, if_false]))
  ... = ∑' (a a' : α), ite (a' = a) ⁅= (a, a) | oa⁆ 0 : by simp_rw [@eq_comm]
  ... = ∑' (a : α), ⁅= (a, a) | oa⁆ : tsum_congr (λ a, tsum_ite_eq _ _)

@[simp] lemma prob_event_fst_eq_snd [decidable_eq α] (oa : oracle_comp spec (α × α)) :
  ⁅λ x, x.1 = x.2 | oa⁆ = ∑' a : α, ⁅= (a, a) | oa⁆ :=
prob_event_diagonal oa

@[simp] lemma prob_event_diagonal_eq_sum [decidable_eq α] [fintype α] (oa : oracle_comp spec (α × α)) :
  ⁅set.diagonal α | oa⁆ = ∑ a : α, ⁅= (a, a) | oa⁆ :=
(prob_event_diagonal oa).trans (tsum_eq_sum (λ x hx, (hx (finset.mem_univ _)).elim))

@[simp] lemma prob_event_fst_eq_snd_eq_sum [decidable_eq α] [fintype α] (oa : oracle_comp spec (α × α)) :
  ⁅λ x, x.1 = x.2 | oa⁆ = ∑ a : α, ⁅= (a, a) | oa⁆ :=
prob_event_diagonal_eq_sum oa

-- @[simp] lemma prob_event_fst_eq (oa : oracle_comp spec (α × β)) (x : α) :
--   ⁅λ z, z.1 = x | oa⁆ = ⁅= x | fst <$> oa⁆ :=
-- by apply prob_event_eq_eq_prob_output_map

-- @[simp] lemma prob_event_snd_eq (oa : oracle_comp spec (α × β)) (y : β) :
--   ⁅λ z, z.2 = y | oa⁆ = ⁅= y | snd <$> oa⁆ :=
-- by simpa only [prob_output_map_eq_tsum_indicator, prob_event_eq_tsum_indicator, ennreal.tsum_prod']

end prob_event

variables (oa : oracle_comp spec α) (f : α → β) (g : α → γ) (b : β) (c : γ)

section bind_prod_mk

section support

lemma support_bind_prod_mk : (oa >>= λ a, return (f a, g a)).support =
  (λ a, (f a, g a)) '' oa.support := support_bind_return oa _

lemma support_map_prod_mk : ((λ a, (f a, g a) : α → β × γ) <$> oa).support =
  (λ a, (f a, g a)) '' oa.support := support_map oa _

lemma mem_support_bind_prod_mk (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ y ∈ oa.support, f y = x.1 ∧ g y = x.2 :=
by simp only [support_bind_return, set.mem_image, exists_prop, eq_iff_fst_eq_snd_eq]

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
by simp_rw [support_bind_prod_mk, set.mem_image, eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_right, and_assoc, @eq_comm γ c]

lemma mem_support_bind_prod_mk_snd (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, g a)).support ↔ x.1 = b ∧ x.2 ∈ g '' oa.support :=
by simp_rw [support_bind_prod_mk, set.mem_image, eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_left, @eq_comm β b, ← and_assoc, and_comm (x.1 = b)]

end support

section fin_support

variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

lemma fin_support_bind_prod_mk :
  (oa >>= λ a, return (f a, g a)).fin_support = oa.fin_support.image (λ a, (f a, g a)) :=
fin_support_bind_return oa _

lemma mem_fin_support_bind_prod_mk (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).fin_support ↔ ∃ y ∈ oa.fin_support, f y = x.1 ∧ g y = x.2 :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk]

lemma mem_fin_support_bind_prod_mk_id_fst (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, g a)).fin_support ↔ x.1 ∈ oa.fin_support ∧ g x.1 = x.2 :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_id_fst]

lemma mem_fin_support_bind_prod_mk_id_snd (x : β × α) :
  x ∈ (oa >>= λ a, return (f a, a)).fin_support ↔ x.2 ∈ oa.fin_support ∧ f x.2 = x.1  :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_id_snd]

lemma mem_fin_support_bind_prod_mk_fst (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).fin_support ↔ x.1 ∈ oa.fin_support.image f ∧ x.2 = c :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_fst,
  set.mem_image, finset.mem_image, exists_prop]

lemma mem_fin_support_bind_prod_mk_snd (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, g a)).fin_support ↔ x.1 = b ∧ x.2 ∈ oa.fin_support.image g :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_snd,
  set.mem_image, finset.mem_image, exists_prop]

end fin_support

section prob_output

@[simp] lemma prob_output_bind_prod_mk (z : α × β)
  (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  ⁅= z | do {x ← oa, y ← ob, return (x, y)}⁆ =
    ⁅= z.1 | oa⁆ * ⁅= z.2 | ob⁆ :=
by rw [← mprod, prob_output_mprod]

@[simp] lemma prob_output_bind_prod_mk_fst
  (x : β × γ) : ⁅= x | oa >>= λ a, return (f a, c)⁆ =
    ⁅= x.1 | f <$> oa⁆ * ⁅= x.2 | return' !spec! c⁆ :=
begin
  cases x with y z,
  by_cases hz : z = c,
  { induction hz,
    simp only [prob_output_bind_eq_tsum, map_eq_bind_pure_comp, prob_output_return_prod_mk_fst,
      prob_output_return_self, mul_one]},
  { simp only [hz, prob_output_bind_eq_tsum, (prob_output_return_eq_zero_iff spec _ _).2 hz,
      mul_zero, ennreal.tsum_eq_zero, mul_eq_zero, prob_output_eq_zero_iff, support_return,
      set.mem_singleton_iff, mk.inj_iff, and_false, not_false_iff, or_true, implies_true_iff] }
end

@[simp] lemma prob_output_bind_prod_mk_snd
  (x : β × γ) : ⁅= x | oa >>= λ a, return (b, g a)⁆ =
    ⁅= x.1 | return' !spec! b⁆ * ⁅= x.2 | g <$> oa⁆ :=
begin
  cases x with y z,
  by_cases hz : y = b,
  { induction hz,
    simp only [prob_output_bind_eq_tsum, map_eq_bind_pure_comp, prob_output_return_prod_mk_snd,
      prob_output_return_self, one_mul]},
  { simp only [hz, prob_output_bind_eq_tsum, (prob_output_return_eq_zero_iff spec _ _).2 hz,
      zero_mul, ennreal.tsum_eq_zero, mul_eq_zero, prob_output_eq_zero_iff, support_return,
      set.mem_singleton_iff, mk.inj_iff, false_and, not_false_iff, or_true, implies_true_iff] }
end

end prob_output

end bind_prod_mk

section bind_prod_mk_subsingleton

section support

@[simp] lemma support_bind_prod_mk_of_fst_subsingleton [subsingleton β] :
  (oa >>= λ a, return (f a, g a)).support = snd ⁻¹' (g '' oa.support) :=
set.ext (λ x, by simp only [support_bind_prod_mk, set.mem_image, set.mem_preimage,
  eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, true_and])

@[simp] lemma support_bind_prod_mk_of_snd_subsingleton [subsingleton γ] :
  (oa >>= λ a, return (f a, g a)).support = fst ⁻¹' (f '' oa.support) :=
set.ext (λ x, by simp only [support_bind_prod_mk, set.mem_image, set.mem_preimage,
  eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, and_true])

lemma mem_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, f a = x.1 :=
by simp_rw [support_bind_prod_mk_of_snd_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

lemma mem_support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, g a = x.2 :=
by simp_rw [support_bind_prod_mk_of_fst_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

end support

section fin_support

variables [decidable_eq α]

@[simp] lemma fin_support_bind_prod_mk_fst_of_subsingleton [decidable_eq β] [subsingleton γ] :
  (oa >>= λ a, return (f a, g a)).fin_support = (oa.fin_support.image f).preimage fst
    (λ y hy z hz h, eq_iff_fst_eq_snd_eq.2 ⟨h, subsingleton.elim _ _⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk, finset.mem_preimage, finset.mem_image,
  eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, and_true])

@[simp] lemma fin_support_bind_prod_mk_snd_of_subsingleton [decidable_eq γ] [subsingleton β] :
  (oa >>= λ a, return (f a, g a)).fin_support = (oa.fin_support.image g).preimage snd
    (λ y hy z hz h, eq_iff_fst_eq_snd_eq.2 ⟨subsingleton.elim _ _, h⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk, finset.mem_preimage, finset.mem_image,
  eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, true_and])

lemma mem_fin_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, f a = x.1 :=
by simp_rw [support_bind_prod_mk_of_snd_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

lemma mem_fin_support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, g a = x.2 :=
by simp_rw [support_bind_prod_mk_of_fst_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

end fin_support

end bind_prod_mk_subsingleton

section bind_bind_prod_mk

variables (ob : α → oracle_comp spec β)

@[simp] lemma support_bind_bind_prod_mk :
  (do {x ← oa, y ← (ob x), return (x, y)}).support =
    {z | z.1 ∈ oa.support ∧ z.2 ∈ (ob z.1).support} :=
set.ext (λ z, by simp [prod.eq_iff_fst_eq_snd_eq])

end bind_bind_prod_mk

end oracle_comp