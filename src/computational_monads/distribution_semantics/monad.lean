/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.return
import computational_monads.distribution_semantics.bind

/-!
# Probability Distributions of Monadic Oracle Constructions

This file gives additional lemmas about how distribution semantics of `bind` and `return` interact.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

section return_bind

variables (a : α) (ob : α → oracle_comp spec β) (y : β) (e' : set β)

lemma support_return_bind : (return a >>= ob).support = (ob a).support :=
by simp only [support_bind, mem_support_return_iff, set.Union_Union_eq_left]

lemma mem_support_return_bind_iff : y ∈ (return a >>= ob).support ↔ y ∈ (ob a).support :=
by rw [support_return_bind]

lemma fin_support_return_bind : (return a >>= ob).fin_support = (ob a).fin_support :=
by simp only [fin_support_bind, fin_support_return, finset.singleton_bUnion]

lemma mem_fin_support_return_bind_iff :
  y ∈ (return a >>= ob).fin_support ↔ y ∈ (ob a).fin_support :=
by rw [fin_support_return_bind]

lemma return_bind_dist_equiv : return a >>= ob ≃ₚ ob a :=
by simp only [dist_equiv.def, eval_dist_bind, eval_dist_return, pmf.pure_bind]

lemma eval_dist_return_bind : ⁅return a >>= ob⁆ = ⁅ob a⁆ :=
(return_bind_dist_equiv a ob).eval_dist_eq

lemma eval_dist_return_bind_apply : ⁅= y | return a >>= ob⁆ = ⁅= y | ob a⁆ :=
(return_bind_dist_equiv a ob).eval_dist_apply_eq y

@[simp] lemma prob_event_return_bind : ⁅e' | return a >>= ob⁆ = ⁅e' | ob a⁆ :=
(return_bind_dist_equiv a ob).prob_event_eq e'

end return_bind

section bind_return

variables (oa : oracle_comp spec α) (f : α → β) (y : β) (e' : set β)

@[simp] lemma support_bind_return : (oa >>= λ x, return (f x)).support = f '' oa.support :=
calc (oa >>= λ x, return (f x)).support = ⋃ x ∈ oa.support, {f x} : rfl
  ... = f '' (⋃ x ∈ oa.support, {x}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

lemma mem_support_bind_return_iff :
  y ∈ (oa >>= λ x, return (f x)).support ↔ ∃ x ∈ oa.support, f x = y :=
by simp only [support_bind_return, set.mem_image, exists_prop]

@[simp] lemma fin_support_bind_return [decidable_eq β] :
  (oa >>= λ a, return (f a)).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, support_bind_return,
  finset.coe_image, coe_fin_support_eq_support]

lemma mem_fin_support_bind_return_iff [decidable_eq β] :
  y ∈ (oa >>= λ a, return (f a)).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by simp only [fin_support_bind_return, finset.mem_image]

@[simp] lemma eval_dist_bind_return : ⁅oa >>= λ x, return (f x)⁆ = ⁅oa⁆.map f :=
by simp_rw [eval_dist_bind, eval_dist_return, pmf.bind_pure_comp]


lemma eval_dist_bind_return_apply_eq_tsum [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑' x, ite (y = f x) (⁅oa⁆ x) 0 :=
begin
  rw [eval_dist_bind_return, pmf.map_apply],
  congr,
  refine funext (λ x, _),
  congr,
end

-- TODO: gross proof
lemma eval_dist_bind_return_apply_eq_tsum_indicator :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
begin
  rw [eval_dist_bind_apply_eq_tsum],
  refine tsum_congr (λ x, _),
  rw [eval_dist_return, pmf.pure_apply, set.indicator],
  rw [mul_ite, mul_one, mul_zero, @eq_comm _ y],
  congr,
end

lemma eval_dist_bind_return_apply_eq_sum [fintype α] [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x, ite (y = f x) (⁅oa⁆ x) 0 :=
(eval_dist_bind_return_apply_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim))

lemma eval_dist_bind_return_apply_eq_sum_indicator [fintype α] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
(eval_dist_bind_return_apply_eq_tsum_indicator oa f y).trans
  (tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim))

lemma eval_dist_bind_return_apply_eq_sum_fin_support [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
(eval_dist_bind_return_apply_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, by rw [eval_dist_eq_zero' hx, if_t_t]))

lemma eval_dist_bind_return_apply_eq_sum_fin_support_indicator :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
(eval_dist_bind_return_apply_eq_tsum_indicator oa f y).trans
  (tsum_eq_sum (λ x hx, by simp_rw [set.indicator_apply_eq_zero,
    eval_dist_eq_zero_iff', hx, not_false_iff, imp_true_iff]))

@[simp] lemma prob_event_bind_return : ⁅e' | oa >>= λ a, return (f a)⁆ = ⁅f ⁻¹' e' | oa⁆ :=
begin
  rw [prob_event_bind_eq_tsum, prob_event_eq_tsum_indicator],
  refine tsum_congr (λ x, by simpa only [prob_event_return_eq_indicator, set.indicator, mul_boole])
end

end bind_return

section bind_return_id

variables (oa : oracle_comp spec α) (y : β) (e' : set β)

@[simp] lemma support_bind_return_id : (oa >>= return).support = oa.support :=
(support_bind_return oa id).trans (set.image_id oa.support)

@[simp] lemma fin_support_bind_return_id [decidable_eq α] :
  (oa >>= return).fin_support = oa.fin_support :=
(fin_support_bind_return oa id).trans finset.image_id

lemma bind_return_id_dist_equiv : oa >>= return ≃ₚ oa :=
(eval_dist_bind_return oa id).trans (by rw [pmf.map_id])

@[simp] lemma eval_dist_bind_return_id : ⁅oa >>= return⁆ = ⁅oa⁆ :=
(bind_return_id_dist_equiv oa).eval_dist_eq

@[simp] lemma prob_event_bind_return_id (e : set α) : ⁅e | oa >>= return⁆ = ⁅e | oa⁆ :=
by rw [prob_event_bind_return, set.preimage_id']

end bind_return_id

section bind_return_eq_single

variables (oa : oracle_comp spec α) (f : α → β) (y : β) (e' : set β)

lemma eval_dist_bind_return_apply_eq_single' (x : α) (hx : f x = y)
  (h : ∀ x' ∈ oa.support, f x' = y → x' = x) : ⁅oa >>= λ x, return (f x)⁆ y = ⁅oa⁆ x :=
begin
  rw [eval_dist_bind_return_apply_eq_tsum_indicator],
  refine trans (tsum_eq_single x $ λ x' hx', set.indicator_apply_eq_zero.2 _) _,
  { exact λ hx'', eval_dist_eq_zero (λ hxs, hx' (h x' hxs hx'')) },
  { simp only [set.mem_preimage, set.mem_singleton_iff, hx, set.indicator_of_mem] }
end

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma eval_dist_bind_return_apply_eq_single (x : α) (hx : f ⁻¹' {y} = {x}) :
  ⁅oa >>= λ x, return (f x)⁆ y = ⁅oa⁆ x :=
begin
  simp only [eval_dist_bind_return_apply_eq_tsum_indicator, hx],
  refine trans (tsum_eq_single x _) (by simp only [set.indicator_of_mem, set.mem_singleton]),
  simp only [set.indicator_apply_eq_zero, eval_dist_eq_zero_iff],
  refine (λ _ h h', (h h').elim),
end

end bind_return_eq_single

end oracle_comp