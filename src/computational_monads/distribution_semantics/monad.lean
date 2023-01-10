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

namespace distribution_semantics

open oracle_comp oracle_spec
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
by { rw [eval_dist_bind_return, pmf.map_apply], exact (tsum_congr $ λ _, by congr) }

lemma eval_dist_bind_return_apply_eq_tsum_preimage :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
begin
  rw [eval_dist_bind_return, pmf.map_apply],
  refine tsum_congr (λ x, _),
  split_ifs with hx,
  { simp only [hx, set.indicator_of_mem, set.mem_preimage, set.mem_singleton] },
  { refine (set.indicator_of_not_mem (by simpa using ne.symm hx) _).symm }
end

lemma eval_dist_bind_return_apply_eq_sum [fintype α] [decidable_eq β] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x, ite (y = f x) (⁅oa⁆ x) 0 :=
(eval_dist_bind_return_apply_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim))

lemma eval_dist_bind_return_apply_eq_sum_fin_support [decidable_eq β] [oa.decidable] :
  ⁅oa >>= λ x, return (f x)⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
(eval_dist_bind_return_apply_eq_tsum oa f y).trans
  (tsum_eq_sum (λ x hx, by rw [eval_dist_eq_zero_of_not_mem_fin_support hx, if_t_t]))

@[simp] lemma eval_dist_bind_return_id : ⁅oa >>= return⁆ = ⁅oa⁆ :=
(eval_dist_bind_return oa id).trans (by rw [pmf.map_id])

/-- If a function `f` returns `y` only when the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma eval_dist_bind_return_apply_eq_single (x : α) (hx : ∀ x' ≠ x, y ≠ f x') (hy : y = f x) :
  ⁅oa >>= λ x, return (f x)⁆ y = ⁅oa⁆ x :=
begin
  rw [eval_dist_bind_return, pmf.map_apply],
  refine (tsum_eq_single x $ λ x' hx', _).trans (by rw [hy, eq_self_iff_true, if_true]),
  rw [ite_eq_right_iff],
  exact λ hy', (hx x' hx' hy').elim,
end

end bind_return

section map

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (oc : β → oracle_comp spec γ)
  (f : α → β) (g : β → γ) (x : α) (y : β)

@[simp] lemma eval_dist_map : ⁅f <$> oa⁆ = ⁅oa⁆.map f := eval_dist_bind oa (pure ∘ f)

lemma eval_dist_map_apply_eq_tsum [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑' x, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_tsum oa _ y

lemma eval_dist_map_apply_eq_sum [fintype α] [decidable_eq β] :
  ⁅f <$> oa⁆ y = ∑ x, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_sum oa _ y

lemma eval_dist_map_apply_eq_sum_fin_support [decidable_eq β] [oa.decidable] :
  ⁅f <$> oa⁆ y = ∑ x in oa.fin_support, ite (y = f x) (⁅oa⁆ x) 0 :=
eval_dist_bind_return_apply_eq_sum_fin_support oa _ y

end map

section map_return

variables (a : α) (f : α → β)

lemma eval_dist_map_return : ⁅f <$> (return a : oracle_comp spec α)⁆ = pmf.pure (f a) :=
by simp [eval_dist_map, pmf.map_pure]

end map_return

section map_bind

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (g : β → γ)

lemma eval_dist_map_bind : ⁅g <$> (oa >>= ob)⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆.map g) :=
by simp only [eval_dist_map, eval_dist_bind, pmf.map_bind]

end map_bind

section bind_map

variables (oa : oracle_comp spec α) (f : α → β) (oc : β → oracle_comp spec γ)

lemma eval_dist_bind_map : ⁅(f <$> oa) >>= oc⁆ = (⁅oa⁆.map f).bind (λ y, ⁅oc y⁆) :=
by simp only [eval_dist_bind, eval_dist_map]

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

end distribution_semantics