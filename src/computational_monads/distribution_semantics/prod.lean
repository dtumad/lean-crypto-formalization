/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.seq
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

@[simp] lemma map_seq_prod_mk_eta (z : α × β) :
  prod.mk <$> return z.1 <*> return z.2 = (return z : oracle_comp spec (α × β)) :=
begin
  rw [map_return, oracle_comp.seq_return],
  simp only [map_pure, seq_pure, mk.eta],
end

@[simp] lemma prob_output_prod_return (z z' : α × β) :
  ⁅= z | (return z' : oracle_comp spec (α × β))⁆ =
    ⁅= z.1 | (return z'.1 : oracle_comp spec α)⁆ *
      ⁅= z.2 | (return z'.2 : oracle_comp spec β)⁆ :=
begin
  rw [← map_seq_prod_mk_eta z', ← @prod.mk.eta _ _ z],
  refine prob_output_seq_map_eq_mul_of_injective2 _ _ prod.mk_injective2 _ _,
end

lemma prob_output_return_prod_mk_fst (x x' : α) (y : β) :
  ⁅= (x, y) | return' !spec! (x', y)⁆ = ⁅= x | return' !spec! x'⁆ :=
by simp

lemma prob_output_return_prod_mk_snd (x : α) (y y' : β) :
  ⁅= (x, y) | return' !spec! (x, y')⁆ = ⁅= y | return' !spec! y'⁆ :=
by simp

@[simp] lemma prob_event_fst_eq_snd_eq (oa : oracle_comp spec (α × β)) (x : α) (y : β) :
  ⁅λ z, z.1 = x ∧ z.2 = y | oa⁆ = ⁅= (x, y) | oa⁆ :=
by simp_rw [← prob_event_eq_eq_prob_output', eq_iff_fst_eq_snd_eq]

@[simp] lemma prob_event_eq_fst_eq_snd (oa : oracle_comp spec (α × β)) (x : α) (y : β) :
  ⁅λ z, x = z.1 ∧ y = z.2 | oa⁆ = ⁅= (x, y) | oa⁆ :=
by simp_rw [← prob_event_eq_eq_prob_output', eq_iff_fst_eq_snd_eq, @eq_comm _ x, @eq_comm _ y]

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

end fst_snd_map_bind_return_dist_equiv

section unused

variables (oa : oracle_comp spec (α × β))

-- @[simp] lemma bind_eq_fst_bind_of_unused (oc : α → oracle_comp spec γ) :
--   oa >>= (λ x, oc x.1) = (fst <$> oa) >>= oc :=
-- by rw [oracle_comp.bind_map] --only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

-- @[simp] lemma bind_eq_snd_bind_of_unused (oc' : β → oracle_comp spec γ) :
--   oa >>= (λ x, oc' x.2) = (snd <$> oa) >>= oc' :=
-- by rw [oracle_comp.bind_map] --only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
-- -- by simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

-- @[pairwise_dist_equiv] lemma bind_dist_equiv_fst_bind_of_unused (oc : α → oracle_comp spec γ) :
--   oa >>= (λ x, oc x.1) ≃ₚ (fst <$> oa) >>= oc :=
-- by rw [oracle_comp.bind_map] --only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

-- -- by rw_dist_equiv [bind_map_dist_equiv]

-- @[pairwise_dist_equiv] lemma bind_dist_equiv_snd_bind_of_unused (oc' : β → oracle_comp spec γ) :
--   oa >>= (λ x, oc' x.2) ≃ₚ (snd <$> oa) >>= oc' :=
-- by rw [oracle_comp.bind_map] --only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

-- -- by rw_dist_equiv [bind_map_dist_equiv]

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

lemma prob_event_prod_bind (p : γ → Prop) :
  ⁅p | oa >>= oc⁆ = ∑' (a : α) (b : β), ⁅= (a, b) | oa⁆ * ⁅p | oc (a, b)⁆ :=
by rw [prob_event_bind_eq_tsum, ennreal.tsum_prod']

lemma prob_event_prod_bind' (p : γ → Prop) :
  ⁅p | oa >>= oc⁆ = ∑' (b : β) (a : α), ⁅= (a, b) | oa⁆ * ⁅p | oc (a, b)⁆ :=
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
  rw [prob_output_map_eq_tsum_ite, ennreal.tsum_prod'],
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
  rw [prob_output_map_eq_tsum_ite, ennreal.tsum_prod', ennreal.tsum_comm],
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
  rw [oracle_comp.bind_map],
  pairwise_dist_equiv [h],
end

lemma bind_dist_equiv_snd_bind (oc : α × β → oracle_comp spec γ) (x : α)
  (h : ∀ z, oc z ≃ₚ oc (x, z.2)) : oa >>= oc ≃ₚ (snd <$> oa >>= λ y, oc (x, y)) :=
begin
  rw [oracle_comp.bind_map],
  pairwise_dist_equiv [h],
end

end fst_snd_map_bind

section diagonal

@[simp] lemma prob_event_mem_diagonal_eq_tsum [decidable_eq α] (oa : oracle_comp spec (α × α)) :
  ⁅(∈ set.diagonal α) | oa⁆ = ∑' a : α, ⁅= (a, a) | oa⁆ :=
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
prob_event_mem_diagonal_eq_tsum oa

@[simp] lemma prob_event_mem_diagonal_eq_sum [decidable_eq α] [fintype α]
  (oa : oracle_comp spec (α × α)) : ⁅(∈ set.diagonal α) | oa⁆ = ∑ a : α, ⁅= (a, a) | oa⁆ :=
(prob_event_mem_diagonal_eq_tsum oa).trans (tsum_eq_sum (λ x hx, (hx (finset.mem_univ _)).elim))

@[simp] lemma prob_event_fst_eq_snd_eq_sum [decidable_eq α] [fintype α]
  (oa : oracle_comp spec (α × α)) : ⁅λ x, x.1 = x.2 | oa⁆ = ∑ a : α, ⁅= (a, a) | oa⁆ :=
prob_event_mem_diagonal_eq_sum oa

end diagonal

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
begin
  refine trans (congr_arg (prob_output _) (prod.mk.eta.symm)) _,
  refine trans _ (prob_output_seq_map_eq_mul_of_injective2 _ _ (prod.mk_injective2) z.1 z.2),
  rw [seq_map_eq_bind_bind],
end

@[simp] lemma prob_output_bind_prod_mk_fst' [decidable_eq β] (z : β × α) :
  ⁅= z | oa >>= λ a, return (f a, a)⁆ = if z.1 = f z.2 then ⁅= z.2 | oa⁆ else 0 :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  cases z with y x,
  by_cases hy : y = f x,
  { simp only [hy, eq_self_iff_true, if_true, prob_output_bind_return_eq_tsum,
      eq_iff_fst_eq_snd_eq],
    refine trans (tsum_eq_single x _) (if_pos ⟨rfl, rfl⟩),
    refine λ x' hx', ite_eq_right_iff.2 (λ hx, (hx' hx.2.symm).elim) },
  { simp only [hy, if_false, prob_output_eq_zero_iff, support_bind_return, set.mem_image,
      mk.inj_iff, exists_eq_right_right, not_and],
    refine λ _, ne.symm hy }
end

@[simp] lemma prob_output_bind_prod_mk_snd' [decidable_eq β] (z : α × β) :
  ⁅= z | oa >>= λ a, return (a, f a)⁆ = if z.2 = f z.1 then ⁅= z.1 | oa⁆ else 0 :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  cases z with x y,
  by_cases hy : y = f x,
  { simp only [hy, eq_self_iff_true, if_true, prob_output_bind_return_eq_tsum,
      eq_iff_fst_eq_snd_eq],
    refine trans (tsum_eq_single x _) (if_pos ⟨rfl, rfl⟩),
    refine λ x' hx', ite_eq_right_iff.2 (λ hx, (hx' hx.1.symm).elim) },
  { simp only [hy, if_false, prob_output_eq_zero_iff, support_bind_return, set.mem_image,
      mk.inj_iff, not_exists, not_and], 
    refine λ _ _ h, h.symm ▸ ne.symm hy }
end

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

lemma support_bind_bind_prod_mk' :
  (do {x ← oa, y ← (ob x), return (x, y)}).support =
    ⋃ x ∈ oa.support, prod.mk x '' (ob x).support :=
by simp

@[simp] lemma support_bind_bind_prod_mk :
  (do {x ← oa, y ← (ob x), return (x, y)}).support =
    {z | z.1 ∈ oa.support ∧ z.2 ∈ (ob z.1).support} :=
set.ext (λ z, by simp only [prod.eq_iff_fst_eq_snd_eq, support_bind, support_bind_return,
  set.mem_Union, set.mem_image, exists_eq_right_right, exists_prop, set.mem_set_of_eq])

-- @[simp] lemma fin_support_bind_bind_prod_mk [decidable_eq α] [decidable_eq β] :
--   (do {x ← oa, y ← (ob x), return (x, y)}).fin_support =
--     oa.fin_support.image (λ x, (ob x).fin_support.image (prod.mk x))

end bind_bind_prod_mk

section map_prod_mk

@[simp] lemma prob_output_map_prod_mk_snd_snd [decidable_eq γ] (oa : oracle_comp spec (α × β))
  (c : γ) (z : α × β × γ) : ⁅= z | (λ xy : α × β, (xy.1, xy.2, c)) <$> oa⁆ =
    if z.2.2 = c then ⁅= (z.1, z.2.1) | oa⁆ else 0 :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  haveI : decidable_eq β := classical.dec_eq β,
  simp only [prob_output_map_eq_tsum_ite, prod.eq_iff_fst_eq_snd_eq],
  refine trans (tsum_eq_single (z.1, z.2.1) (λ xy hxy, if_neg _)) _,
  { simp [prod.eq_iff_fst_eq_snd_eq] at ⊢ hxy,
    exact λ h' h'', (hxy h'.symm h''.symm).elim },
  { simp only [eq_self_iff_true, true_and] }
end

end map_prod_mk

end oracle_comp