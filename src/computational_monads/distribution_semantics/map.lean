/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad

/-!
# Distribution Semantics of Map

This file gives various lemmas for probability outcomes of the computation `f <$> oa`.
-/

namespace oracle_comp

open_locale ennreal big_operators

variables {α β γ : Type} {spec spec' : oracle_spec} (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : β → oracle_comp spec γ)
  (f : α → β) (g : β → γ) (x : α) (y : β) (z : γ)

section support

@[simp] lemma support_map : (f <$> oa).support = f '' oa.support :=
support_bind_return oa f

lemma mem_support_map_iff : y ∈ (f <$> oa).support ↔ ∃ x ∈ oa.support, f x = y :=
mem_support_bind_return_iff oa f y

@[simp] lemma fin_support_map [decidable_eq β] : (f <$> oa).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_image,
  support_map, coe_fin_support_eq_support]

lemma mem_fin_support_map_iff [decidable_eq β] :
  y ∈ (f <$> oa).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by rw [fin_support_map, finset.mem_image]

end support

section eval_dist

@[simp] lemma eval_dist_map : ⁅f <$> oa⁆ = ⁅oa⁆.map f := eval_dist_bind oa (pure ∘ f)

lemma eval_dist_map_apply_eq_tsum [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑' x, if y = f x then ⁅oa⁆ x else 0 :=
eval_dist_bind_return_apply_eq_tsum oa f y

lemma eval_dist_map_apply_eq_tsum_indicator :
  ⁅= y | f <$> oa⁆ = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_tsum_indicator oa f y

lemma eval_dist_map_apply_eq_sum [fintype α] [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑ x, if y = f x then ⁅oa⁆ x else 0 :=
eval_dist_bind_return_apply_eq_sum oa f y

lemma eval_dist_map_apply_eq_sum_indicator [fintype α] :
  ⁅= y | f <$> oa⁆ = ∑ x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_sum_indicator oa f y

lemma eval_dist_map_apply_eq_sum_fin_support [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑ x in oa.fin_support, if y = f x then ⁅oa⁆ x else 0 :=
eval_dist_bind_return_apply_eq_sum_fin_support oa f y

lemma eval_dist_map_apply_eq_sum_fin_support_indicator :
  ⁅= y | f <$> oa⁆ = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_sum_fin_support_indicator oa f y

end eval_dist

section prob_event

variable (e : set β)

@[simp] lemma prob_event_map : ⁅e | f <$> oa⁆ = ⁅f ⁻¹' e | oa⁆ :=
prob_event_bind_return oa f e

lemma prob_event_map_eq_tsum_indicator : ⁅e | f <$> oa⁆ = ∑' x, (f ⁻¹' e).indicator ⁅oa⁆ x :=
by rw [prob_event_map, prob_event_eq_tsum_indicator]

lemma prob_event_map_apply_eq_tsum [decidable_pred (∈ e)] :
  ⁅e | f <$> oa⁆ = ∑' x, if f x ∈ e then ⁅oa⁆ x else 0 :=
(prob_event_map_eq_tsum_indicator oa f e).trans
  (tsum_congr (λ x, by simp only [set.indicator, set.mem_preimage]))

end prob_event

section map_return

variable (a : α)

@[simp_dist_equiv] lemma map_return_dist_equiv :
  f <$> (return a : oracle_comp spec α) ≃ₚ (return (f a) : oracle_comp spec β) :=
by simp only [dist_equiv.def, eval_dist_map, eval_dist_return, pmf.map_pure]

lemma support_map_return : (f <$> (return a : oracle_comp spec α)).support = {f a} :=
by simp only [support_map, support_return, set.image_singleton]

lemma mem_support_map_return_iff : y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

lemma fin_support_map_return [decidable_eq α] [decidable_eq β] :
  (f <$> (return a : oracle_comp spec α)).fin_support = {f a} :=
by simp only [fin_support_map, fin_support_return, finset.image_singleton]

lemma mem_fin_support_map_return_iff [decidable_eq α] [decidable_eq β] :
  y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

lemma eval_dist_map_return : ⁅f <$> (return a : oracle_comp spec α)⁆ = pmf.pure (f a) :=
by simp only [eval_dist_map, eval_dist_return, pmf.map_pure]

lemma eval_dist_map_return' : ⁅f <$> (return a : oracle_comp spec α)⁆ =
  ⁅(return (f a) : oracle_comp spec β)⁆ := eval_dist_map_return f a

lemma prob_event_map_return (e : set β) : ⁅e | f <$> (return a : oracle_comp spec α)⁆ =
  ⁅e | (return (f a) : oracle_comp spec β)⁆ :=
prob_event_eq_of_eval_dist_eq (by rw [eval_dist_map_return, eval_dist_return]) e

end map_return

section map_comp

@[simp_dist_equiv] lemma map_comp_dist_equiv : g <$> (f <$> oa) ≃ₚ (g ∘ f) <$> oa :=
by simp only [dist_equiv.def, eval_dist_map, pmf.map_comp]

lemma eval_dist_map_comp : ⁅g <$> (f <$> oa)⁆ = ⁅oa⁆.map (g ∘ f) :=
by simp only [eval_dist_map, pmf.map_comp]

lemma prob_event_map_comp (e : set γ) : ⁅e | g <$> (f <$> oa)⁆ = ⁅e | (g ∘ f) <$> oa⁆ :=
by pairwise_dist_equiv

end map_comp

section map_bind

@[simp] lemma support_map_bind : (g <$> (oa >>= ob)).support =
  ⋃ a ∈ oa.support, g '' (ob a).support :=
by simp_rw [support_map, support_bind, set.image_Union]

lemma mem_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).support ↔
  ∃ x ∈ oa.support, ∃ y ∈ (ob x).support, g y = z :=
by simp only [support_map_bind, set.mem_Union, set.mem_image, exists_prop]

@[simp] lemma fin_support_map_bind [decidable_eq γ] : (g <$> (oa >>= ob)).fin_support =
  finset.bUnion oa.fin_support (λ a, (ob a).fin_support.image g) :=
by simp_rw [fin_support_eq_iff_support_eq_coe, finset.coe_bUnion, finset.coe_image,
  coe_fin_support_eq_support, support_map_bind]

lemma mem_fin_support_map_bind_iff [decidable_eq γ] : z ∈ (g <$> (oa >>= ob)).fin_support ↔
  ∃ x ∈ oa.fin_support, ∃ y ∈ (ob x).fin_support, g y = z :=
by simp only [fin_support_map_bind, finset.mem_bUnion, finset.mem_image]

@[simp_dist_equiv] lemma map_bind_dist_equiv : g <$> (oa >>= ob) ≃ₚ oa >>= (λ x, g <$> ob x) :=
by simp only [dist_equiv.def, eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_map_bind : ⁅g <$> (oa >>= ob)⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆.map g) :=
by simp only [eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_map_bind' : ⁅g <$> (oa >>= ob)⁆ = ⁅oa >>= (λ x, g <$> (ob x))⁆ :=
by pairwise_dist_equiv

lemma eval_dist_map_bind_apply_eq_tsum [decidable_eq γ] :
  ⁅= z | g <$> (oa >>= ob)⁆ = ∑' (x : α) (y : β), ⁅oa⁆ x * (ite (z = g y) (⁅ob x⁆ y) 0) :=
by simp only [eval_dist_map_bind', eval_dist_bind_apply_eq_tsum,
  eval_dist_map_apply_eq_tsum, ennreal.tsum_mul_left]

lemma eval_dist_map_bind_apply_eq_sum [fintype α] [fintype β] [decidable_eq γ] :
  ⁅= z | g <$> (oa >>= ob)⁆ = ∑ (x : α) (y : β), ⁅oa⁆ x * (ite (z = g y) (⁅ob x⁆ y) 0) :=
by simp_rw [eval_dist_map_bind', eval_dist_bind_apply_eq_sum,
  eval_dist_map_apply_eq_sum, ← finset.mul_sum]

lemma eval_dist_map_bind_apply_eq_sum_fin_support [decidable_eq γ] : ⁅= z | g <$> (oa >>= ob)⁆ =
  ∑ x in oa.fin_support, ∑ y in (ob x).fin_support, ⁅oa⁆ x * (ite (z = g y) (⁅ob x⁆ y) 0) :=
by simp_rw [eval_dist_map_bind', eval_dist_bind_apply_eq_sum_fin_support,
  eval_dist_map_apply_eq_sum_fin_support, ← finset.mul_sum]

lemma prob_event_map_bind (e' : set γ) :
  ⁅e' | g <$> (oa >>= ob)⁆ = ⁅e' | oa >>= λ x, g <$> (ob x)⁆ :=
by pairwise_dist_equiv

end map_bind

section bind_map

lemma support_bind_map : ((f <$> oa) >>= oc).support =
  ⋃ x ∈ oa.support, (oc (f x)).support :=
by simp only [support_bind, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

lemma mem_support_bind_map_iff : z ∈ ((f <$> oa) >>= oc).support ↔
  ∃ x ∈ oa.support, z ∈ (oc (f x)).support :=
by simp only [support_bind, set.mem_Union, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

@[simp] lemma fin_support_bind_map [decidable_eq β] [decidable_eq γ] :
  ((f <$> oa) >>= oc).fin_support =
  finset.bUnion oa.fin_support (λ a, (oc (f a)).fin_support) :=
by simp only [finset.image_bUnion, fin_support_bind, fin_support_map]; congr

lemma mem_fin_support_bind_map_iff [decidable_eq β] [decidable_eq γ] :
  z ∈ ((f <$> oa) >>= oc).fin_support ↔ ∃ x ∈ oa.fin_support, z ∈ (oc (f x)).fin_support :=
by simp only [fin_support_bind_map, finset.mem_bUnion]

lemma eval_dist_bind_map : ⁅(f <$> oa) >>= oc⁆ = ⁅oa⁆.bind (λ y, ⁅oc (f y)⁆) :=
by simp only [eval_dist_bind, eval_dist_map, pmf.bind_map]

lemma eval_dist_bind_map' : ⁅(f <$> oa) >>= oc⁆ = ⁅oa >>= oc ∘ f⁆ :=
by simp only [eval_dist_bind, eval_dist_map, pmf.bind_map]

lemma eval_dist_bind_map_apply_eq_tsum :
  ⁅(f <$> oa) >>= oc⁆ z = ∑' (x : α), ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
by rw [eval_dist_bind_map, pmf.bind_apply]

lemma eval_dist_bind_map_apply_eq_sum [fintype α] :
  ⁅(f <$> oa) >>= oc⁆ z = ∑ (x : α), ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
begin
  rw [eval_dist_bind_map, pmf.bind_apply],
  exact tsum_eq_sum (λ _ h, (h $ finset.mem_univ _).elim),
end

lemma eval_dist_bind_map_apply_eq_sum_fin_support :
  ⁅(f <$> oa) >>= oc⁆ z = ∑ x in oa.fin_support, ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
begin
  rw [eval_dist_bind_map, pmf.bind_apply],
  refine tsum_eq_sum (λ x hx, _),
  simp only [mul_eq_zero, eval_dist_eq_zero_iff'],
  exact or.inl hx,
end

end bind_map

section map_id

@[simp_dist_equiv] lemma map_id_dist_equiv : id <$> oa ≃ₚ oa :=
by rw [dist_equiv.def, eval_dist_map, ⁅oa⁆.map_id]

@[simp] lemma support_map_id : (id <$> oa).support = oa.support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_map_id : (id <$> oa).fin_support = oa.fin_support :=
by pairwise_dist_equiv

@[simp] lemma eval_dist_map_id : ⁅id <$> oa⁆ = ⁅oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_map_id (e : set α) : ⁅e | id <$> oa⁆ = ⁅e | oa⁆ :=
by pairwise_dist_equiv

end map_id

section eq_single

lemma eval_dist_map_apply_eq_single' (hx : f x = y) (h : ∀ x' ∈ oa.support, f x' = y → x' = x) :
  ⁅= y | f <$> oa⁆ = ⁅= x | oa⁆ := eval_dist_bind_return_apply_eq_single' oa f y x hx h

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma eval_dist_map_apply_eq_single (hx : f ⁻¹' {y} = {x}) :
  ⁅= y | f <$> oa⁆ = ⁅= x | oa⁆ := eval_dist_bind_return_apply_eq_single oa f y x hx

lemma eval_dist_map_apply_of_injective (hf : f.injective) : ⁅=f x | f <$> oa⁆ = ⁅= x | oa⁆ :=
eval_dist_map_apply_eq_single' oa f x (f x) rfl (λ x' hx' hxf, hf hxf)

end eq_single

end oracle_comp