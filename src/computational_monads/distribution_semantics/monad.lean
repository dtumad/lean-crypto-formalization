/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.eval_dist

/-!
# Probability Distributions of Monadic Oracle Constructions

This file defines additional lemmas about the distribution semantics of constructions
given by a composition of monad operations.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec : oracle_spec}

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

lemma eval_dist_bind_return_apply_eq_sum_fin_support [oa.decidable] [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
(eval_dist_bind_return_apply_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, by rw [eval_dist_eq_zero_of_not_mem_fin_support hx, if_t_t]))

lemma eval_dist_bind_return_apply_eq_sum_fin_support_indicator [oa.decidable] [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
(eval_dist_bind_return_apply_eq_tsum_indicator oa f y).trans
  (tsum_eq_sum (λ x hx, by simp_rw [set.indicator_apply_eq_zero,
    eval_dist_eq_zero_iff_not_mem_fin_support, hx, not_false_iff, imp_true_iff]))

@[simp] lemma eval_dist_bind_return_id : ⁅oa >>= return⁆ = ⁅oa⁆ :=
(eval_dist_bind_return oa id).trans (by rw [pmf.map_id])

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma eval_dist_bind_return_apply_eq_single [decidable_eq β]
  (x : α) (hx : f ⁻¹' {y} = {x}) : ⁅oa >>= λ x, return (f x)⁆ y = ⁅oa⁆ x :=
begin
  simp only [eval_dist_bind_return_apply_eq_tsum_indicator, hx],
  refine trans (tsum_eq_single x _) (by simp only [set.indicator_of_mem, set.mem_singleton]),
  simp only [set.indicator_apply_eq_zero, eval_dist_eq_zero_iff_not_mem_support],
  refine (λ _ h h', (h h').elim),
end

end bind_return

section map

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (oc : β → oracle_comp spec γ)
  (f : α → β) (g : β → γ) (x : α) (y : β)

@[simp] lemma eval_dist_map : ⁅f <$> oa⁆ = ⁅oa⁆.map f := eval_dist_bind oa (pure ∘ f)

lemma eval_dist_map_apply_eq_tsum [decidable_eq β] : ⁅f <$> oa⁆ y = ∑' x, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_tsum oa f y

lemma eval_dist_map_apply_eq_tsum_indicator [decidable_eq β] : ⁅f <$> oa⁆ y = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_tsum_indicator oa f y

lemma eval_dist_map_apply_eq_sum [fintype α] [decidable_eq β] : ⁅f <$> oa⁆ y = ∑ x, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_sum oa f y

lemma eval_dist_map_apply_eq_sum_indicator [fintype α] [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑ x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_sum_indicator oa f y

lemma eval_dist_map_apply_eq_sum_fin_support [oa.decidable] [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_sum_fin_support oa f y

lemma eval_dist_map_apply_eq_sum_fin_support_indicator [oa.decidable] [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
eval_dist_bind_return_apply_eq_sum_fin_support_indicator oa f y

@[simp] lemma eval_dist_map_id : ⁅id <$> oa⁆ = ⁅oa⁆ := by rw [eval_dist_map, ⁅oa⁆.map_id]

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma eval_dist_map_apply_eq_single [decidable_eq β] (x : α) (hx : f ⁻¹' {y} = {x}) :
  ⁅f <$> oa⁆ y = ⁅oa⁆ x := eval_dist_bind_return_apply_eq_single oa f y x hx

end map

section map_return

variables (a : α) (f : α → β)

lemma eval_dist_map_return : ⁅f <$> (return a : oracle_comp spec α)⁆ = pmf.pure (f a) :=
by simp [eval_dist_map, pmf.map_pure]

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

lemma eval_dist_map_bind_apply_eq_sum_fin_support [decidable oa] [∀ x, decidable (ob x)] [decidable_eq γ] :
  ⁅g <$> (oa >>= ob)⁆ z = ∑ x in oa.fin_support, ∑ y in (ob x).fin_support, ⁅oa⁆ x * (ite (z = g y) (⁅ob x⁆ y) 0) :=
by simp_rw [eval_dist_map_bind', eval_dist_bind_apply_eq_sum_fin_support,
  eval_dist_map_apply_eq_sum_fin_support, ← finset.mul_sum]

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

lemma eval_dist_bind_map_apply_eq_sum_fin_support [decidable oa] :
  ⁅(f <$> oa) >>= oc⁆ z = ∑ x in oa.fin_support, ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
begin
  rw [eval_dist_bind_map, pmf.bind_apply],
  refine tsum_eq_sum (λ x hx, _),
  simp only [mul_eq_zero, eval_dist_eq_zero_iff_not_mem_fin_support],
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

end oracle_comp