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

section bind_bind_assoc

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (oc : β → oracle_comp spec γ)

/-- Bind operations are associative under distributional equivalence.
Intentionally avoid making this a `simp_dist_equiv` lemma, as it can be counterproductive. -/
@[pairwise_dist_equiv]
lemma bind_bind_dist_equiv_assoc : oa >>= (λ x, ob x >>= oc) ≃ₚ oa >>= ob >>= oc :=
dist_equiv.ext (λ x, by simp only [prob_output.def, eval_dist_bind, pmf.bind_bind])

lemma support_bind_bind_assoc : (oa >>= (λ x, ob x >>= oc)).support = (oa >>= ob >>= oc).support :=
by pairwise_dist_equiv [bind_bind_dist_equiv_assoc]

lemma fin_support_bind_bind_assoc : (oa >>= (λ x, ob x >>= oc)).fin_support =
  (oa >>= ob >>= oc).fin_support := by pairwise_dist_equiv [bind_bind_dist_equiv_assoc]

lemma prob_output_bind_bind_assoc (z : γ) :
  ⁅= z | oa >>= (λ x, ob x >>= oc)⁆ = ⁅= z | oa >>= ob >>= oc⁆ :=
by pairwise_dist_equiv [bind_bind_dist_equiv_assoc]

lemma prob_event_bind_bind_assoc (e : set γ) :
  ⁅e | oa >>= (λ x, ob x >>= oc)⁆ = ⁅e | (oa >>= ob) >>= oc⁆ :=
by pairwise_dist_equiv [bind_bind_dist_equiv_assoc]

end bind_bind_assoc

section bind_bind_dist_equiv_comm

variables (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (oc : α → β → oracle_comp spec γ)

@[pairwise_dist_equiv] lemma bind_bind_dist_equiv_comm :
  do {a ← oa, b ← ob, oc a b} ≃ₚ do {b ← ob, a ← oa, oc a b} :=
begin
  simp only [dist_equiv.ext_iff, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left, ← mul_assoc],
  refine λ z, ennreal.tsum_comm.trans (tsum_congr (λ y, by simp_rw [mul_comm ⁅= y | ob⁆]))
end

end bind_bind_dist_equiv_comm

section return_bind

variables (a : α) (ob : α → oracle_comp spec β) (y : β) (e' : set β)

@[simp_dist_equiv] lemma return_bind_dist_equiv : return a >>= ob ≃ₚ ob a :=
by simp only [dist_equiv.def, eval_dist_bind, eval_dist_return, pmf.pure_bind]

lemma support_return_bind : (return a >>= ob).support = (ob a).support :=
by pairwise_dist_equiv

lemma fin_support_return_bind : (return a >>= ob).fin_support = (ob a).fin_support :=
by pairwise_dist_equiv

lemma eval_dist_return_bind : ⁅return a >>= ob⁆ = ⁅ob a⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_output_return_bind : ⁅= y | return a >>= ob⁆ = ⁅= y | ob a⁆ :=
(return_bind_dist_equiv a ob).prob_output_eq y

@[simp] lemma prob_event_return_bind : ⁅e' | return a >>= ob⁆ = ⁅e' | ob a⁆ :=
by pairwise_dist_equiv

end return_bind

section bind_return

variables (oa : oracle_comp spec α) (f : α → β) (y : β) (e' : set β)

section support

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

end support

section eval_dist

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

lemma prob_output_bind_return_eq_sum_fin_support [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
(prob_output_bind_return_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, by rw [prob_output_eq_zero' hx, if_t_t]))

lemma prob_output_bind_return_eq_sum_fin_support_indicator :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
(prob_output_bind_return_eq_tsum_indicator oa f y).trans
  (tsum_eq_sum (λ x hx, set.indicator_apply_eq_zero.2 (λ h, prob_output_eq_zero' hx)))

end eval_dist

section prob_event

@[simp] lemma prob_event_bind_return : ⁅e' | oa >>= λ a, return (f a)⁆ = ⁅f ⁻¹' e' | oa⁆ :=
begin
  rw [prob_event_bind_eq_tsum, prob_event_eq_tsum_indicator],
  refine tsum_congr (λ x, by simpa only [prob_event_return_eq_indicator, set.indicator, mul_boole])
end

end prob_event

end bind_return

section bind_return_id

variables (oa : oracle_comp spec α) (y : β) (e' : set β)

@[simp_dist_equiv] lemma bind_return_id_dist_equiv : oa >>= return ≃ₚ oa :=
(eval_dist_bind_return oa id).trans (by rw [pmf.map_id])

@[simp] lemma support_bind_return_id : (oa >>= return).support = oa.support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_bind_return_id [decidable_eq α] :
  (oa >>= return).fin_support = oa.fin_support := by pairwise_dist_equiv

@[simp] lemma eval_dist_bind_return_id : ⁅oa >>= return⁆ = ⁅oa⁆ := by pairwise_dist_equiv

@[simp] lemma prob_output_bind_return_id (x : α) : ⁅= x | oa >>= return⁆ = ⁅= x | oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_bind_return_id (e : set α) : ⁅e | oa >>= return⁆ = ⁅e | oa⁆ :=
by pairwise_dist_equiv

end bind_return_id

section bind_const

variables (oa : oracle_comp spec α) (ob : oracle_comp spec β)

@[simp_dist_equiv] lemma bind_const_dist_equiv : oa >>= (λ _, ob) ≃ₚ ob :=
by rw [dist_equiv.def, eval_dist_bind, pmf.bind_const]

@[simp] lemma support_bind_const : (oa >>= (λ _, ob)).support = ob.support :=
(bind_const_dist_equiv oa ob).support_eq

@[simp] lemma fin_support_bind_const : (oa >>= (λ _, ob)).fin_support = ob.fin_support :=
(bind_const_dist_equiv oa ob).fin_support_eq

@[simp] lemma eval_dist_bind_const : ⁅oa >>= (λ _, ob)⁆ = ⁅ob⁆ :=
(bind_const_dist_equiv oa ob).eval_dist_eq

@[simp] lemma prob_output_bind_const (x : β) : ⁅= x | oa >>= (λ _, ob)⁆ = ⁅= x | ob⁆ :=
(bind_const_dist_equiv oa ob).prob_output_eq x

@[simp] lemma prob_event_bind_const (e : set β) : ⁅e | oa >>= (λ _, ob)⁆ = ⁅e | ob⁆ :=
(bind_const_dist_equiv oa ob).prob_event_eq e

end bind_const

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

end oracle_comp