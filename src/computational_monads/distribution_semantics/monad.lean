/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.return
import computational_monads.distribution_semantics.bind
import computational_monads.distribution_semantics.query


/-!
# Probability Distributions of Monadic Oracle Constructions

This file defines additional lemmas about the distribution semantics of constructions
given by a composition of monad operations.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

section return_bind

variables (a : α) (ob : α → oracle_comp spec β) (y : β)

lemma eval_dist_return_bind : ⁅return a >>= ob⁆ = ⁅ob a⁆ :=
by simp only [eval_dist_bind, eval_dist_return, pmf.pure_bind]

lemma eval_dist_return_bind_apply : ⁅return a >>= ob⁆ y = ⁅ob a⁆ y :=
by simp only [eval_dist_bind, eval_dist_return, pmf.pure_bind]

end return_bind

section bind_return

variables (oa : oracle_comp spec α) (f : α → β) (y : β)

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

lemma eval_dist_bind_return_apply_eq_sum_indicator [fintype α] [decidable_eq β] :
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

@[simp] lemma eval_dist_bind_return_id : ⁅oa >>= return⁆ = ⁅oa⁆ :=
(eval_dist_bind_return oa id).trans (by rw [pmf.map_id])

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

end bind_return

section map

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (oc : β → oracle_comp spec γ)
  (f : α → β) (g : β → γ) (x : α) (y : β)

@[simp] lemma eval_dist_map : ⁅f <$> oa⁆ = ⁅oa⁆.map f := eval_dist_bind oa (pure ∘ f)

lemma eval_dist_map_comp' : ⁅g <$> (f <$> oa)⁆ = ⁅(g ∘ f) <$> oa⁆ :=
by simp only [eval_dist_map, pmf.map_comp]

lemma eval_dist_map_apply_eq_tsum [decidable_eq β] : ⁅f <$> oa⁆ y = ∑' x, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_tsum oa f y

lemma eval_dist_map_apply_eq_tsum_indicator : ⁅f <$> oa⁆ y = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_tsum_indicator oa f y

lemma eval_dist_map_apply_eq_sum [fintype α] [decidable_eq β] : ⁅f <$> oa⁆ y = ∑ x, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_sum oa f y

lemma eval_dist_map_apply_eq_sum_indicator [fintype α] [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑ x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_sum_indicator oa f y

lemma eval_dist_map_apply_eq_sum_fin_support [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_sum_fin_support oa f y

lemma eval_dist_map_apply_eq_sum_fin_support_indicator [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_sum_fin_support_indicator oa f y

@[simp] lemma eval_dist_map_id : ⁅id <$> oa⁆ = ⁅oa⁆ := by rw [eval_dist_map, ⁅oa⁆.map_id]

lemma eval_dist_map_apply_eq_single' (x : α) (hx : f x = y)
  (h : ∀ x' ∈ oa.support, f x' = y → x' = x) : ⁅f <$> oa⁆ y = ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_single' oa f y x hx h

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma eval_dist_map_apply_eq_single (x : α) (hx : f ⁻¹' {y} = {x}) :
  ⁅f <$> oa⁆ y = ⁅oa⁆ x := eval_dist_bind_return_apply_eq_single oa f y x hx

lemma eval_dist_map_apply_of_injective (x : α) (hf : f.injective) : ⁅f <$> oa⁆ (f x) = ⁅oa⁆ x :=
eval_dist_map_apply_eq_single' oa f (f x) x rfl (λ x' hx' hxf, hf hxf)

lemma map_equiv_congr {f f' : α → β} {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (hf : ∀ x, f x = f' x) (hoa : oa ≃ₚ oa') : (f <$> oa) ≃ₚ (f' <$> oa') :=
dist_equiv.ext (λ x, by simp only [eval_dist_map, hoa.eval_dist_eq, (funext hf : f = f')])

end map

section map_return

variables (a : α) (f : α → β)

lemma eval_dist_map_return : ⁅f <$> (return a : oracle_comp spec α)⁆ = pmf.pure (f a) :=
by simp only [eval_dist_map, eval_dist_return, pmf.map_pure]

end map_return

section map_bind

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (g : β → γ) (z : γ)

lemma eval_dist_map_bind : ⁅g <$> (oa >>= ob)⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆.map g) :=
by simp only [eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_map_bind' : ⁅g <$> (oa >>= ob)⁆ = ⁅oa >>= (λ x, g <$> (ob x))⁆ :=
by simp only [eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_map_bind_apply_eq_tsum [decidable_eq γ] :
  ⁅g <$> (oa >>= ob)⁆ z = ∑' (x : α) (y : β), ⁅oa⁆ x * (ite (z = g y) (⁅ob x⁆ y) 0) :=
by simp only [eval_dist_map_bind', eval_dist_bind_apply_eq_tsum,
  eval_dist_map_apply_eq_tsum, ennreal.tsum_mul_left]

lemma eval_dist_map_bind_apply_eq_sum [fintype α] [fintype β] [decidable_eq γ] :
  ⁅g <$> (oa >>= ob)⁆ z = ∑ (x : α) (y : β), ⁅oa⁆ x * (ite (z = g y) (⁅ob x⁆ y) 0) :=
by simp_rw [eval_dist_map_bind', eval_dist_bind_apply_eq_sum,
  eval_dist_map_apply_eq_sum, ← finset.mul_sum]

lemma eval_dist_map_bind_apply_eq_sum_fin_support [decidable_eq γ] :
  ⁅g <$> (oa >>= ob)⁆ z = ∑ x in oa.fin_support, ∑ y in (ob x).fin_support, ⁅oa⁆ x * (ite (z = g y) (⁅ob x⁆ y) 0) :=
sorry
-- by simp_rw [eval_dist_map_bind', eval_dist_bind_apply_eq_sum_fin_support,
--   eval_dist_map_apply_eq_sum_fin_support, ← finset.mul_sum]

end map_bind

section bind_map

variables (oa : oracle_comp spec α) (f : α → β) (oc : β → oracle_comp spec γ) (z : γ)

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

section query_bind

variables (i : spec.ι) (t : spec.domain i) (oa : spec.range i → oracle_comp spec α) (x : α)

lemma eval_dist_query_bind_apply_eq_tsum :
  ⁅query i t >>= oa⁆ x = (∑' u, ⁅oa u⁆ x) / (fintype.card $ spec.range i) :=
by simp_rw [eval_dist_bind_apply_eq_tsum, eval_dist_query_apply, div_eq_mul_inv,
  one_mul, ennreal.tsum_mul_left, mul_comm]

lemma eval_dist_query_bind_apply_eq_sum :
  ⁅query i t >>= oa⁆ x = (∑ u, ⁅oa u⁆ x) / (fintype.card $ spec.range i) :=
by simp_rw [eval_dist_bind_apply_eq_sum, eval_dist_query_apply, div_eq_mul_inv,
  one_mul, finset.sum_mul, mul_comm]

end query_bind


-- TODO: feels like the wrong file for this
section ite

variables (oa : oracle_comp spec α) (p : α → Prop) (f g : α → β) (x : α) (y : β)

lemma eval_dist_bind_ite_apply_eq_tsum_add_tsum [decidable_pred p] [decidable_eq β] :
  ⁅oa >>= λ a, return (if p a then f a else g a)⁆ y =
    (∑' x, ite (p x ∧ y = f x) (⁅oa⁆ x) 0) + (∑' x, ite (¬ p x ∧ y = g x) (⁅oa⁆ x) 0) :=
begin
  rw [eval_dist_bind_return_apply_eq_tsum, ← ennreal.tsum_add],
  refine tsum_congr (λ x, _),
  by_cases hpx : p x;
  simp only [hpx, if_true, true_and, not_true, false_and, if_false, add_zero,
    if_false, false_and, not_false_iff, true_and, zero_add]
end

lemma eval_dist_bind_ite_apply_eq_sum_add_sum [fintype α] [decidable_pred p] [decidable_eq β] :
  ⁅oa >>= λ a, return (if p a then f a else g a)⁆ y =
    (∑ x, ite (p x ∧ y = f x) (⁅oa⁆ x) 0) + (∑ x, ite (¬ p x ∧ y = g x) (⁅oa⁆ x) 0) :=
begin
  rw [eval_dist_bind_return_apply_eq_sum, ← finset.sum_add_distrib],
  refine finset.sum_congr rfl (λ x _, _),
  by_cases hpx : p x;
  simp only [hpx, if_true, true_and, not_true, false_and, if_false, add_zero,
    if_false, false_and, not_false_iff, true_and, zero_add],
end

end ite






section return_bind

variables (a : α) (ob : α → oracle_comp spec β) (y : β)

lemma support_return_bind : (return a >>= ob).support = (ob a).support :=
by simp only [support_bind, mem_support_return_iff, set.Union_Union_eq_left]

lemma mem_support_return_bind_iff : y ∈ (return a >>= ob).support ↔ y ∈ (ob a).support :=
by rw [support_return_bind]

variables [decidable_eq α]

lemma fin_support_return_bind : (return a >>= ob).fin_support = (ob a).fin_support :=
by simp only [fin_support_bind, fin_support_return, finset.singleton_bUnion]

lemma mem_fin_support_return_bind_iff :
  y ∈ (return a >>= ob).fin_support ↔ y ∈ (ob a).fin_support :=
by rw [fin_support_return_bind]

end return_bind

section bind_return

variables (oa : oracle_comp spec α) (f : α → β) (y : β)

@[simp] lemma support_bind_return : (oa >>= λ x, return (f x)).support = f '' oa.support :=
calc (f <$> oa).support = ⋃ x ∈ oa.support, {f x} : rfl
  ... = f '' (⋃ x ∈ oa.support, {x}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

lemma mem_support_bind_return_iff :
  y ∈ (oa >>= λ x, return (f x)).support ↔ ∃ x ∈ oa.support, f x = y :=
by simp only [support_bind_return, set.mem_image, exists_prop]

@[simp] lemma support_bind_return_id : (oa >>= return).support = oa.support :=
(support_bind_return oa id).trans (set.image_id oa.support)

@[simp] lemma fin_support_bind_return [decidable_eq β] :
  (oa >>= λ a, return (f a)).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, support_bind_return,
  finset.coe_image, coe_fin_support_eq_support]

lemma mem_fin_support_bind_return_iff [decidable_eq β] :
  y ∈ (oa >>= λ a, return (f a)).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by simp only [fin_support_bind_return, finset.mem_image]

@[simp] lemma fin_support_bind_return_id [decidable_eq α] :
  (oa >>= return).fin_support = oa.fin_support :=
(fin_support_bind_return oa id).trans finset.image_id

end bind_return

section query_bind

variables (i : spec.ι) (t : spec.domain i) (oa : spec.range i → oracle_comp spec α) (x : α)

lemma support_query_bind : (query i t >>= oa).support = ⋃ u, (oa u).support :=
by simp only [support_bind, set.Union_true]

lemma mem_support_query_bind_iff : x ∈ (query i t >>= oa).support ↔ ∃ t, x ∈ (oa t).support :=
by rw [support_query_bind, set.mem_Union]

variables [decidable_eq α]

lemma fin_support_query_bind : (query i t >>= oa).fin_support =
  finset.bUnion finset.univ (λ u, (oa u).fin_support) :=
by {simp only [fin_support_bind, fin_support_query, finset.top_eq_univ], congr}

lemma mem_fin_support_query_bind_iff :
  x ∈ (query i t >>= oa).fin_support ↔ ∃ t, x ∈ (oa t).fin_support :=
by simp only [fin_support_query_bind, finset.mem_bUnion, finset.mem_univ, exists_true_left]

end query_bind

section map

variables (oa : oracle_comp spec α) (f : α → β)  (y : β)

@[simp] lemma support_map : (f <$> oa).support = f '' oa.support :=
support_bind_return oa f

lemma mem_support_map_iff : y ∈ (f <$> oa).support ↔ ∃ x ∈ oa.support, f x = y :=
mem_support_bind_return_iff oa f y

variables [decidable_eq β]

@[simp] lemma fin_support_map : (f <$> oa).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_image,
  support_map, coe_fin_support_eq_support]

lemma mem_fin_support_map_iff : y ∈ (f <$> oa).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by rw [fin_support_map, finset.mem_image]

end map

section map_return

variables (a : α) (f : α → β) (y : β)

lemma support_map_return : (f <$> (return a : oracle_comp spec α)).support = {f a} :=
by simp only [support_map, support_return, set.image_singleton]

lemma mem_support_map_return_iff : y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

variables [decidable_eq α] [decidable_eq β]

lemma fin_support_map_return :
  (f <$> (return a : oracle_comp spec α)).fin_support = {f a} :=
by simp only [fin_support_map, fin_support_return, finset.image_singleton]

lemma mem_fin_support_map_return_iff :
  y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

end map_return

section map_bind

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (g : β → γ) (z : γ)

@[simp] lemma support_map_bind : (g <$> (oa >>= ob)).support =
  ⋃ a ∈ oa.support, g '' (ob a).support :=
by simp_rw [support_map, support_bind, set.image_Union]

lemma mem_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).support ↔
  ∃ x ∈ oa.support, ∃ y ∈ (ob x).support, g y = z :=
by simp only [support_map_bind, set.mem_Union, set.mem_image, exists_prop]

variables [decidable_eq γ]

@[simp] lemma fin_support_map_bind : (g <$> (oa >>= ob)).fin_support =
  finset.bUnion oa.fin_support (λ a, (ob a).fin_support.image g) :=
by simp_rw [fin_support_eq_iff_support_eq_coe, finset.coe_bUnion, finset.coe_image,
  coe_fin_support_eq_support, support_map_bind]

lemma mem_fin_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).fin_support ↔
  ∃ x ∈ oa.fin_support, ∃ y ∈ (ob x).fin_support, g y = z :=
by simp only [fin_support_map_bind, finset.mem_bUnion, finset.mem_image]

end map_bind

section bind_map

variables (oa : oracle_comp spec α) (f : α → β) (oc : β → oracle_comp spec γ) (z : γ)

lemma support_bind_map : ((f <$> oa) >>= oc).support =
  ⋃ x ∈ oa.support, (oc (f x)).support :=
by simp only [support_bind, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

lemma mem_support_bind_map_iff : z ∈ ((f <$> oa) >>= oc).support ↔
  ∃ x ∈ oa.support, z ∈ (oc (f x)).support :=
by simp only [support_bind, set.mem_Union, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

variables [decidable_eq β]

@[simp] lemma fin_support_bind_map [decidable_eq γ] : ((f <$> oa) >>= oc).fin_support =
  finset.bUnion oa.fin_support (λ a, (oc (f a)).fin_support) :=
by simp only [finset.image_bUnion, fin_support_bind, fin_support_map]; congr

lemma mem_fin_support_bind_map_iff [decidable_eq γ] : z ∈ ((f <$> oa) >>= oc).fin_support ↔
  ∃ x ∈ oa.fin_support, z ∈ (oc (f x)).fin_support :=
by simp only [fin_support_bind_map, finset.mem_bUnion]

end bind_map

-- TODO: This doesn't really belong in this file
@[simp] lemma support_bind_ite (oa : oracle_comp spec α) (p : α → Prop) [decidable_pred p]
  (f g : α → β) : (oa >>= λ a, return (if p a then f a else g a)).support =
  (f '' {x ∈ oa.support | p x}) ∪ (g '' {x ∈ oa.support | ¬ p x}) :=
begin
  refine set.ext (λ x, _),
  simp only [mem_support_bind_return_iff, set.mem_union,
    set.mem_image, exists_prop, set.mem_sep_iff],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨x, hx⟩ := h,
    by_cases hpx : p x,
    { rw [if_pos hpx] at hx,
      exact or.inl ⟨x, ⟨hx.1, hpx⟩, hx.2⟩ },
    { rw [if_neg hpx] at hx,
      exact or.inr ⟨x, ⟨hx.1, hpx⟩, hx.2⟩ } },
  { cases h with h h,
    { obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := h,
      exact ⟨x, hx, if_pos hx'⟩ },
    { obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := h,
      exact ⟨x, hx, if_neg hx'⟩ } }
end

@[simp] lemma fin_support_bind_ite [decidable_eq β] (oa : oracle_comp spec α)
  (p : α → Prop) [decidable_pred p] (f : α → β) (g : α → β) :
  (oa >>= λ a, return (if p a then f a else g a)).fin_support =
    ((oa.fin_support.filter p).image f) ∪ ((oa.fin_support.filter (not ∘ p)).image g) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind_ite, finset.coe_union,
  finset.coe_image, finset.coe_filter, coe_fin_support_eq_support]


end oracle_comp