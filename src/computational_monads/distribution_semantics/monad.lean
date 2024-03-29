/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.pairwise_dist_equiv

/-!
# Probability Distributions of Monadic Oracle Constructions

This file gives additional lemmas about how distribution semantics of `bind` and `return` interact.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

lemma return_bind_dist_equiv (a : α) (oa : α → oracle_comp spec β) :
  return a >>= oa ≃ₚ oa a := dist_equiv.rfl

@[pairwise_dist_equiv] lemma bind_return_dist_equiv (oa : oracle_comp spec α) :
  oa >>= return ≃ₚ oa := by rw [oracle_comp.bind_return]

@[pairwise_dist_equiv] lemma bind_dist_equiv_assoc (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : β → oracle_comp spec γ) :
  oa >>= (λ x, ob x >>= oc) ≃ₚ oa >>= ob >>= oc := by rw [bind_assoc]

section bind_bind_comm

variables (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (oc : α → β → oracle_comp spec γ)

@[pairwise_dist_equiv] lemma bind_bind_dist_equiv_comm :
  do {a ← oa, b ← ob, oc a b} ≃ₚ do {b ← ob, a ← oa, oc a b} :=
begin
  simp only [dist_equiv.ext_iff, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left, ← mul_assoc],
  refine λ z, ennreal.tsum_comm.trans (tsum_congr (λ y, by simp_rw [mul_comm ⁅= y | ob⁆]))
end

lemma support_bind_bind_comm : (do {a ← oa, b ← ob, oc a b}).support =
  (do {b ← ob, a ← oa, oc a b}).support := by pairwise_dist_equiv

lemma fin_support_bind_bind_comm : (do {a ← oa, b ← ob, oc a b}).support =
  (do {b ← ob, a ← oa, oc a b}).support := by pairwise_dist_equiv

lemma prob_output_bind_bind_comm (z : γ) : ⁅= z | do {a ← oa, b ← ob, oc a b}⁆ =
  ⁅= z | do {b ← ob, a ← oa, oc a b}⁆ := by pairwise_dist_equiv

lemma prob_event_bind_bind_comm (p : γ → Prop) : ⁅p | do {a ← oa, b ← ob, oc a b}⁆ =
  ⁅p | do {b ← ob, a ← oa, oc a b}⁆ := by pairwise_dist_equiv

end bind_bind_comm

section bind_return

variables (oa : oracle_comp spec α) (f : α → β) (y : β) (p : β → Prop)

@[simp] lemma support_bind_return : (oa >>= λ x, return (f x)).support = f '' oa.support :=
calc (oa >>= λ x, return (f x)).support = ⋃ x ∈ oa.support, {f x} :
    by simp only [support_bind, support_return]
  ... = f '' (⋃ x ∈ oa.support, {x}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

lemma mem_support_bind_return_iff :
  y ∈ (oa >>= λ x, return (f x)).support ↔ ∃ x ∈ oa.support, f x = y :=
by simp only [support_bind_return, set.mem_image, exists_prop]

@[simp] lemma fin_support_bind_return [decidable_eq α] [decidable_eq β] :
  (oa >>= λ a, return (f a)).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, support_bind_return,
  finset.coe_image, coe_fin_support]

lemma mem_fin_support_bind_return_iff [decidable_eq α] [decidable_eq β] :
  y ∈ (oa >>= λ a, return (f a)).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by simp only [fin_support_bind_return, finset.mem_image]

@[simp] lemma eval_dist_bind_return : ⁅oa >>= λ x, return (f x)⁆ = ⁅oa⁆.map f :=
by simp_rw [eval_dist_bind, eval_dist_return, pmf.bind_pure_comp]

lemma prob_output_bind_return_eq_tsum [decidable_eq β] :
  ⁅= y | oa >>= λ x, return (f x)⁆ = ∑' x, ite (y = f x) ⁅= x | oa⁆ 0 :=
by simp only [prob_output_bind_eq_tsum, prob_output_return, mul_ite, mul_one, mul_zero]

lemma prob_output_bind_return_eq_tsum_indicator :
  ⁅= y | oa >>= λ x, return (f x)⁆ = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
begin
  refine (prob_output_bind_eq_tsum _ _ _).trans (tsum_congr $ λ x, _),
  rw [set.indicator],
  split_ifs,
  { rw [prob_output_return_of_eq _ (symm h), mul_one, eval_dist_apply_eq_prob_output] },
  { rw [prob_output_return_of_ne _ (ne.symm h), mul_zero] }
end

lemma prob_output_bind_return_eq_sum [fintype α] [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x, ite (y = f x) (⁅oa⁆ x) 0 :=
(prob_output_bind_return_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim))

lemma prob_output_bind_return_eq_sum_indicator [fintype α] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
(prob_output_bind_return_eq_tsum_indicator oa f y).trans
  (tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim))

lemma prob_output_bind_return_eq_sum_fin_support [decidable_eq α] [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
(prob_output_bind_return_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, by rw [prob_output_eq_zero' hx, if_t_t]))

lemma prob_output_bind_return_eq_sum_fin_support_indicator [decidable_eq α] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
(prob_output_bind_return_eq_tsum_indicator oa f y).trans
  (tsum_eq_sum (λ x hx, set.indicator_apply_eq_zero.2 (λ h, prob_output_eq_zero' hx)))

@[simp] lemma prob_event_bind_return : ⁅p | oa >>= λ a, return (f a)⁆ = ⁅p ∘ f | oa⁆ :=
begin
  haveI : decidable_pred p := classical.dec_pred p,
  simp_rw [prob_event_bind_eq_tsum, prob_event_return, mul_ite, mul_one, mul_zero,
    prob_event_eq_tsum_ite]
end

end bind_return

section bind_eq_single

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)

lemma prob_output_bind_eq_single' (y : β) (x : α)
  (hx : ∀ x' ∈ oa.support, y ∈ (ob x').support → x' = x) :
  ⁅= y | oa >>= ob⁆ = ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
begin
  rw [prob_output_bind_eq_tsum],
  refine tsum_eq_single x (λ x' hx', _),
  simp [← not_and_distrib],
  refine (λ h1 h2, hx' (hx x' h1 h2)),
end

end bind_eq_single

section bind_return_eq_single

variables (oa : oracle_comp spec α) (f : α → β) (y : β) (e' : set β)

lemma prob_output_bind_return_eq_single' (x : α) (hx : f x = y)
  (h : ∀ x' ∈ oa.support, f x' = y → x' = x) : ⁅= y | oa >>= λ x, return (f x)⁆ = ⁅= x | oa⁆ :=
begin
  rw [prob_output_bind_return_eq_tsum_indicator, prob_output.def],
  refine trans (tsum_eq_single x $ λ x' hx', set.indicator_apply_eq_zero.2 _) _,
  { exact λ hx'', prob_output_eq_zero (λ hxs, hx' (h x' hxs hx'')) },
  { simp only [set.mem_preimage, set.mem_singleton_iff, hx, set.indicator_of_mem] }
end

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma prob_output_bind_return_eq_single (x : α) (hx : f ⁻¹' {y} = {x}) :
  ⁅= y | oa >>= λ x, return (f x)⁆ = ⁅= x | oa⁆ :=
begin
  simp only [prob_output_bind_return_eq_tsum_indicator, hx],
  exact trans (tsum_eq_single x (λ x' hx', set.indicator_apply_eq_zero.2 (λ h', (hx' h').elim)))
    (set.indicator_apply_eq_self.2 (λ h, (h rfl).elim)),
end

end bind_return_eq_single

section bind_const

variables (oa : oracle_comp spec α) (ob : oracle_comp spec β)

@[simp_dist_equiv] lemma bind_const_dist_equiv : oa >>= (λ _, ob) ≃ₚ ob :=
by rw [dist_equiv.def, eval_dist_bind, pmf.bind_const]

@[simp] lemma bind_const_dist_equiv_iff (ob' : oracle_comp spec β) :
  oa >>= (λ _, ob) ≃ₚ ob' ↔ ob ≃ₚ ob' :=
⟨λ h, (bind_const_dist_equiv _ _).symm.trans h,
  λ h, trans (bind_const_dist_equiv _ _) h⟩

@[simp] lemma dist_equiv_bind_const_iff (ob' : oracle_comp spec β) :
  ob' ≃ₚ oa >>= (λ _, ob) ↔ ob' ≃ₚ ob :=
dist_equiv.symm_iff.trans ((bind_const_dist_equiv_iff oa ob ob').trans dist_equiv.symm_iff)

@[simp] lemma support_bind_const : (oa >>= (λ _, ob)).support = ob.support :=
(bind_const_dist_equiv oa ob).support_eq

@[simp] lemma fin_support_bind_const [decidable_eq β] :
  (oa >>= (λ _, ob)).fin_support = ob.fin_support :=
(bind_const_dist_equiv oa ob).fin_support_eq

@[simp] lemma eval_dist_bind_const : ⁅oa >>= (λ _, ob)⁆ = ⁅ob⁆ :=
(bind_const_dist_equiv oa ob).eval_dist_eq

@[simp] lemma prob_output_bind_const (x : β) : ⁅= x | oa >>= (λ _, ob)⁆ = ⁅= x | ob⁆ :=
(bind_const_dist_equiv oa ob).prob_output_eq x

@[simp] lemma prob_event_bind_const (p : β → Prop) : ⁅p | oa >>= (λ _, ob)⁆ = ⁅p | ob⁆ :=
(bind_const_dist_equiv oa ob).prob_event_eq p

end bind_const

section bind_const_bind

variables (oa : oracle_comp spec α) (ob : oracle_comp spec β) (oc : α → oracle_comp spec γ)

lemma support_bind_const_bind :
  (do {x ← oa, y ← ob, oc x}).support = (oa >>= oc).support := by pairwise_dist_equiv

@[simp] lemma fin_support_const_bind [decidable_eq γ] :
  (do {x ← oa, y ← ob, oc x}).fin_support = (oa >>= oc).fin_support := by pairwise_dist_equiv

@[simp] lemma prob_output_bind_const_bind (z : γ) :
  ⁅= z | do {x ← oa, y ← ob, oc x}⁆ = ⁅= z | oa >>= oc⁆ := by pairwise_dist_equiv

@[simp] lemma prob_event_bind_const_bind (p : γ → Prop) :
  ⁅p | do {x ← oa, y ← ob, oc x}⁆ = ⁅p | oa >>= oc⁆ := by pairwise_dist_equiv

end bind_const_bind

end oracle_comp