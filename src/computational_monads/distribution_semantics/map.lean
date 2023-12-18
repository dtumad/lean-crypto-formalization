/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.rw_dist_equiv

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

@[simp] lemma fin_support_map [decidable_eq α] [decidable_eq β] :
  (f <$> oa).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_image,
  support_map, coe_fin_support_eq_support]

lemma mem_fin_support_map_iff [decidable_eq α] [decidable_eq β] :
  y ∈ (f <$> oa).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by rw [fin_support_map, finset.mem_image]

lemma apply_mem_support_map (hx : x ∈ oa.support) : f x ∈ (f <$> oa).support :=
have ∃ (x' : α), x' ∈ oa.support ∧ f x' = f x := ⟨x, hx, rfl⟩,
  by simp only [this, support_map, set.mem_image]

end support

section eval_dist

@[simp] lemma eval_dist_map : ⁅f <$> oa⁆ = ⁅oa⁆.map f := eval_dist_bind oa (pure ∘ f)

lemma prob_output_map_eq_tsum [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑' x, if y = f x then ⁅= x | oa⁆ else 0 :=
prob_output_bind_return_eq_tsum oa f y

lemma prob_output_map_eq_tsum_indicator :
  ⁅= y | f <$> oa⁆ = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
prob_output_bind_return_eq_tsum_indicator oa f y

lemma prob_output_map_eq_sum [fintype α] [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑ x, if y = f x then ⁅oa⁆ x else 0 :=
prob_output_bind_return_eq_sum oa f y

lemma prob_output_map_eq_sum_indicator [fintype α] :
  ⁅= y | f <$> oa⁆ = ∑ x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
prob_output_bind_return_eq_sum_indicator oa f y

lemma prob_output_map_eq_sum_fin_support [decidable_eq α] [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑ x in oa.fin_support, if y = f x then ⁅oa⁆ x else 0 :=
prob_output_bind_return_eq_sum_fin_support oa f y

lemma prob_output_map_eq_sum_fin_support_indicator [decidable_eq α] :
  ⁅= y | f <$> oa⁆ = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
prob_output_bind_return_eq_sum_fin_support_indicator oa f y

end eval_dist

section prob_output


end prob_output

section prob_event

variable (e : set β)

@[simp] lemma prob_event_map : ⁅e | f <$> oa⁆ = ⁅f ⁻¹' e | oa⁆ :=
prob_event_bind_return oa f e

-- TODO!: we should either stick to predicates or sets probably? maybe not??
lemma prob_event_map' (p : β → Prop) : ⁅p | f <$> oa⁆ = ⁅p ∘ f | oa⁆ :=
by simpa [set.preimage]

example : ⁅e | f <$> oa⁆ = ⁅f ⁻¹' e | oa⁆ := by simp

lemma prob_event_map_eq_tsum_indicator : ⁅e | f <$> oa⁆ = ∑' x, (f ⁻¹' e).indicator ⁅oa⁆ x :=
by rw [prob_event_map, prob_event_eq_tsum_indicator]

lemma prob_event_map_eq_tsum [decidable_pred (∈ e)] :
  ⁅e | f <$> oa⁆ = ∑' x, if f x ∈ e then ⁅oa⁆ x else 0 :=
(prob_event_map_eq_tsum_indicator oa f e).trans
  (tsum_congr (λ x, by simp only [set.indicator, set.mem_preimage]))

@[simp] lemma prob_event_eq_eq_prob_output_map (y : β) (f : α → β) :
  ⁅λ x, f x = y | oa⁆ = ⁅= y | f <$> oa⁆ :=
by simpa only [← prob_event_eq_eq_prob_output, prob_event_map, @eq_comm β _ y, set.preimage]

@[simp] lemma prob_event_eq_eq_prob_output_map' (y : β) (f : α → β) :
  ⁅λ x, y = f x | oa⁆ = ⁅= y | f <$> oa⁆ :=
by simpa only [← prob_event_eq_eq_prob_output, prob_event_map, set.preimage]

end prob_event

lemma map_dist_equiv_bind_return : f <$> oa ≃ₚ oa >>= (λ x, return (f x)) := dist_equiv.rfl

lemma map_dist_equiv_of_dist_equiv {f g : α → β} {oa : oracle_comp spec α}
  {oa' : oracle_comp spec' α} (h : ∀ x ∈ oa.support, f x = g x) (h' : oa ≃ₚ oa') :
  f <$> oa ≃ₚ g <$> oa' :=
bind_dist_equiv_bind_of_dist_equiv h' (λ x hx, by simp [h x hx])

lemma map_dist_equiv_of_dist_equiv' {f g : α → β} {oa : oracle_comp spec α}
  {oa' : oracle_comp spec' α} (h : f = g) (h' : oa ≃ₚ oa') : f <$> oa ≃ₚ g <$> oa' :=
bind_dist_equiv_bind_of_dist_equiv h' (by simp [h])

section map_return

variable (a : α)

/-- This version of a map-return lemma preserves the original `oracle_spec`,
which works well with `rw_dist_equiv`-/
lemma map_return_dist_equiv : f <$> (return' !spec! a) ≃ₚ (return' !spec! (f a)) :=
by rw [map_pure]

/-- This version of a map-return lemma allows for an arbitrary `oracle_spec` on both sides,
which works well with `pairwise_dist_equiv`. -/
@[pairwise_dist_equiv] lemma map_return_dist_equiv' :
  f <$> (return' !spec! a) ≃ₚ (return' !spec'! (f a)) :=
dist_equiv.ext (λ x, rfl)

lemma support_map_return : (f <$> (return' !spec! a)).support = {f a} :=
by simp only [support_map, support_return, set.image_singleton]

lemma mem_support_map_return_iff : y ∈ (f <$> (return' !spec! a)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

lemma fin_support_map_return [decidable_eq β] :
  (f <$> return' !spec! a).fin_support = {f a} :=
by simp only [map_pure, fin_support_return]

lemma mem_fin_support_map_return_iff : y ∈ (f <$> return' !spec! a).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

lemma eval_dist_map_return : ⁅f <$> return' !spec! a⁆ = pmf.pure (f a) :=
by simp only [eval_dist_map, eval_dist_return, pmf.map_pure]

lemma prob_output_map_return (x : β) :
  ⁅= x | f <$> return' !spec! a⁆ = ⁅= x | return' !spec! (f a)⁆ :=
by pairwise_dist_equiv

lemma prob_event_map_return (e : set β) :
  ⁅e | f <$> (return' !spec! a)⁆ = ⁅e | return' !spec! (f a)⁆ :=
by rw [map_pure]

end map_return

section map_comp

@[pairwise_dist_equiv] lemma map_comp_dist_equiv : g <$> (f <$> oa) ≃ₚ (g ∘ f) <$> oa :=
by simp only [map_map_eq_map_comp]

lemma support_map_comp : (g <$> (f <$> oa)).support = ((g ∘ f) <$> oa).support :=
by pairwise_dist_equiv

lemma fin_support_map_comp [decidable_eq γ] :
  (g <$> (f <$> oa)).fin_support = ((g ∘ f) <$> oa).fin_support :=
by pairwise_dist_equiv

lemma eval_dist_map_comp : ⁅g <$> (f <$> oa)⁆ = ⁅oa⁆.map (g ∘ f) :=
by simp only [eval_dist_map, pmf.map_comp]

lemma prob_output_map_comp (x : γ) : ⁅= x | g <$> (f <$> oa)⁆ = ⁅= x | (g ∘ f) <$> oa⁆ :=
by pairwise_dist_equiv

lemma prob_event_map_comp (e : set γ) : ⁅e | g <$> (f <$> oa)⁆ = ⁅e | (g ∘ f) <$> oa⁆ :=
by pairwise_dist_equiv

end map_comp

section map_bind

@[simp] protected lemma map_bind : g <$> (oa >>= ob) = oa >>= λ x, g <$> (ob x) :=
by rw [map_bind]

lemma support_map_bind : (g <$> (oa >>= ob)).support =
  ⋃ a ∈ oa.support, g '' (ob a).support :=
by simp_rw [support_map, support_bind, set.image_Union]

lemma mem_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).support ↔
  ∃ x ∈ oa.support, ∃ y ∈ (ob x).support, g y = z :=
by simp only [support_map_bind, set.mem_Union, set.mem_image, exists_prop]

lemma fin_support_map_bind [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
  (g <$> (oa >>= ob)).fin_support =
    finset.bUnion oa.fin_support (λ a, (ob a).fin_support.image g) :=
by simp only [map_bind, fin_support_bind, fin_support_map]

lemma mem_fin_support_map_bind_iff [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
  z ∈ (g <$> (oa >>= ob)).fin_support ↔
    ∃ x ∈ oa.fin_support, ∃ y ∈ (ob x).fin_support, g y = z :=
by simp only [fin_support_map_bind, finset.mem_bUnion, finset.mem_image]

@[pairwise_dist_equiv] lemma map_bind_dist_equiv : g <$> (oa >>= ob) ≃ₚ oa >>= (λ x, g <$> ob x) :=
by simp only [dist_equiv.def, eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_map_bind : ⁅g <$> (oa >>= ob)⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆.map g) :=
by simp only [eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_map_bind' : ⁅g <$> (oa >>= ob)⁆ = ⁅oa >>= (λ x, g <$> (ob x))⁆ :=
by pairwise_dist_equiv

lemma prob_output_map_bind_eq_tsum [decidable_eq γ] :
  ⁅= z | g <$> (oa >>= ob)⁆ = ∑' (x : α) (y : β), ⁅= x | oa⁆ * (ite (z = g y) (⁅= y | ob x⁆) 0) :=
begin
  simp only [prob_output.def, eval_dist_map_bind, pmf.bind_apply, pmf.map_apply,
    ennreal.tsum_mul_left],
  exact tsum_congr (λ x, congr_arg _ (tsum_congr (λ y, by congr))),
end

lemma prob_output_map_bind_eq_sum [fintype α] [fintype β] [decidable_eq γ] :
  ⁅= z | g <$> (oa >>= ob)⁆ = ∑ (x : α) (y : β), ⁅= x | oa⁆ * (ite (z = g y) ⁅= y | ob x⁆ 0) :=
by simp only [prob_output_map_bind_eq_tsum, tsum_fintype]

lemma prob_output_map_bind_eq_sum_fin_support [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
  ⁅= z | g <$> (oa >>= ob)⁆ = ∑ x in oa.fin_support,
    ∑ y in (ob x).fin_support, ⁅= x | oa⁆ * (ite (z = g y) ⁅= y | ob x⁆ 0) :=
trans ((map_bind_dist_equiv _ _ _).prob_output_eq _) (by simpa only
  [prob_output_bind_eq_sum_fin_support, prob_output_map_eq_sum_fin_support, finset.mul_sum])

lemma prob_event_map_bind (e' : set γ) :
  ⁅e' | g <$> (oa >>= ob)⁆ = ⁅e' | oa >>= λ x, g <$> (ob x)⁆ :=
by pairwise_dist_equiv

lemma map_bind_dist_equiv_left (f : β → α) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : ∀ x ∈ oa.support, f '' (ob x).support = {x}) : f <$> (oa >>= ob) ≃ₚ oa :=
begin
  refine trans (map_bind_dist_equiv _ _ _) _,
  apply bind_dist_equiv_left,
  intros x hx,
  rw [dist_equiv_return_iff', support_map, h x hx],
end

lemma map_bind_dist_equiv_right {f : β → γ} {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  (x : α) (h : ∀ y ∈ oa.support, f <$> ob y ≃ₚ f <$> ob x) :
  f <$> (oa >>= ob) ≃ₚ f <$> (ob x) :=
begin
  refine trans (map_bind_dist_equiv _ _ _) _,
  apply bind_dist_equiv_right,
  exact h,
end

end map_bind

section bind_map

lemma bind_map_dist_equiv : (f <$> oa) >>= oc ≃ₚ oa >>= oc ∘ f :=
by simp only [dist_equiv.def, eval_dist_bind, eval_dist_map, pmf.bind_map]

lemma support_bind_map : ((f <$> oa) >>= oc).support =
  ⋃ x ∈ oa.support, (oc (f x)).support :=
by simp only [support_bind, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

lemma mem_support_bind_map_iff : z ∈ ((f <$> oa) >>= oc).support ↔
  ∃ x ∈ oa.support, z ∈ (oc (f x)).support :=
by simp only [support_bind, set.mem_Union, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

@[simp] lemma fin_support_bind_map [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
  ((f <$> oa) >>= oc).fin_support =
    finset.bUnion oa.fin_support (λ a, (oc (f a)).fin_support) :=
by simp only [finset.image_bUnion, fin_support_bind, fin_support_map]; congr

lemma mem_fin_support_bind_map_iff [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
  z ∈ ((f <$> oa) >>= oc).fin_support ↔ ∃ x ∈ oa.fin_support, z ∈ (oc (f x)).fin_support :=
by simp only [fin_support_bind_map, finset.mem_bUnion]

lemma eval_dist_bind_map : ⁅(f <$> oa) >>= oc⁆ = ⁅oa⁆.bind (λ y, ⁅oc (f y)⁆) :=
by simp only [eval_dist_bind, eval_dist_map, pmf.bind_map]

lemma eval_dist_bind_map' : ⁅(f <$> oa) >>= oc⁆ = ⁅oa >>= oc ∘ f⁆ :=
by pairwise_dist_equiv [bind_map_dist_equiv]

lemma prob_output_bind_map_eq_tsum : ⁅= z | (f <$> oa) >>= oc⁆ =
  ∑' (x : α), ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
trans ((bind_map_dist_equiv _ _ _).prob_output_eq z) (prob_output_bind_eq_tsum _ _ _)

lemma prob_output_bind_map_eq_sum [fintype α] : ⁅= z | (f <$> oa) >>= oc⁆ =
  ∑ (x : α), ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
trans ((bind_map_dist_equiv _ _ _).prob_output_eq z) (prob_output_bind_eq_sum _ _ _)

lemma prob_output_bind_map_eq_sum_fin_support [decidable_eq α] [decidable_eq γ] :
  ⁅= z | (f <$> oa) >>= oc⁆ =
    ∑ x in oa.fin_support, ⁅= x | oa⁆ * ⁅= z | oc (f x)⁆ :=
trans ((bind_map_dist_equiv _ _ _).prob_output_eq z) (prob_output_bind_eq_sum_fin_support _ _ _)

end bind_map

section map_const

variable (b : β)

@[simp_dist_equiv] lemma map_const_dist_equiv : (λ _, b) <$> oa ≃ₚ return' !spec'! b :=
begin
  refine dist_equiv.ext (λ y, _),
  by_cases hy : b = y,
  { simp only [hy, prob_output_eq_one_of_subset, set.subset_singleton_iff, support_map,
      set.mem_image, and_imp, forall_exists_index, forall_apply_eq_imp_iff₂,
      eq_self_iff_true, implies_true_iff, prob_output_return_self] },
  { simp only [prob_output_return_of_ne _ (ne.symm hy), hy, prob_output_eq_zero_iff, support_map,
      set.mem_image, and_false, exists_false, not_false_iff] }
end

@[simp] lemma support_map_const : ((λ _, b) <$> oa).support = {b} :=
by simp [map_eq_bind_pure_comp]

@[simp] lemma fin_support_map_const [decidable_eq β] :
  ((λ _, b) <$> oa).fin_support = {b} :=
by simp only [fin_support_eq_iff_support_eq_coe, support_map_const, finset.coe_singleton]

@[simp] lemma eval_dist_map_const : ⁅(λ _, b) <$> oa⁆ = pmf.pure b :=
trans (by pairwise_dist_equiv) (@eval_dist_pure _ spec b)

@[simp] lemma prob_output_map_const (y : β) : ⁅= y | (λ _, b) <$> oa⁆ = ⁅= y | return' !spec! b⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_map_const (e : set β) : ⁅e | (λ _, b) <$> oa⁆ = ⁅e | return' !spec! b⁆ :=
by pairwise_dist_equiv

end map_const

section eq_single

lemma prob_output_map_eq_single' (hx : f x = y) (h : ∀ x' ∈ oa.support, f x' = y → x' = x) :
  ⁅= y | f <$> oa⁆ = ⁅= x | oa⁆ := prob_output_bind_return_eq_single' oa f y x hx h

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma prob_output_map_eq_single (hx : f ⁻¹' {y} = {x}) :
  ⁅= y | f <$> oa⁆ = ⁅= x | oa⁆ := prob_output_bind_return_eq_single oa f y x hx

lemma prob_output_map_of_injective (hf : f.injective) : ⁅= f x | f <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_eq_single' oa f x (f x) rfl (λ x' hx' hxf, hf hxf)

end eq_single

section cancel

@[simp] lemma prob_output_map_mul_right [has_mul α] [is_right_cancel_mul α]
  (x : α) : ⁅= (*) x | (*) <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_of_injective oa (*) x (λ y y' hg, (mul_left_inj x).1 (congr_fun hg x))

@[simp] lemma prob_output_map_mul_left [has_mul α] [is_left_cancel_mul α]
  (x : α) : ⁅= (* x) | (λ y, (* y)) <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_of_injective oa _ x (λ y y' hg, (mul_right_inj x).1 (congr_fun hg x))

@[simp] lemma prob_output_map_add_right [has_add α] [is_right_cancel_add α]
  (x : α) : ⁅= (+) x | (+) <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_of_injective oa (+) x (λ y y' hg, (add_left_inj x).1 (congr_fun hg x))

@[simp] lemma prob_output_map_add_left [has_add α] [is_left_cancel_add α]
  (x : α) : ⁅= (+ x) | (λ y, (+ y)) <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_of_injective oa _ x (λ y y' hg, (add_right_inj x).1 (congr_fun hg x))

end cancel

lemma prob_output_bind_map_eq_mul (f : α → β → γ) (g1 : γ → α) (g2 : γ → β)
  (h : ∀ x ∈ oa.support, ∀ y ∈ (ob x).support, ∀ z, f x y = z ↔ g1 z = x ∧ g2 z = y) (z : γ) :
  ⁅= z | oa >>= λ a, f a <$> ob a⁆ = ⁅= g1 z | oa⁆ * ⁅= g2 z | ob (g1 z)⁆ :=
begin
  rw [prob_output_bind_eq_tsum],
  refine trans (tsum_eq_single (g1 z) (λ x hx, _)) _,
  { by_cases hxa : x ∈ oa.support,
    { refine mul_eq_zero_of_right _ (prob_output_eq_zero _),
      simp_rw [mem_support_map_iff, not_exists],
      intros y hy,
      simp_rw [h x hxa y hy, not_and_distrib, hx.symm, not_false_iff, true_or] },
    { rw [prob_output_eq_zero hxa, zero_mul] } },
  { by_cases hg1 : g1 z ∈ oa.support,
    { refine congr_arg (λ x, _ * x) _,
      rw [oracle_comp.map_eq_bind_return_comp, prob_output_bind_eq_tsum],
      refine trans (tsum_eq_single (g2 z) (λ y hy, _)) _,
      { by_cases hyb : y ∈ (ob (g1 z)).support,
        { refine mul_eq_zero_of_right _ _,
          simp [@eq_comm _ z, h (g1 z) hg1 y hyb z, hy.symm, ← ne.def] },
        { rw [prob_output_eq_zero hyb, zero_mul] } },
      { by_cases hg2 : g2 z ∈ (ob (g1 z)).support,
        { refine trans (congr_arg (λ e, _ * e) _) (mul_one _),
          exact (prob_output_return_eq_one_iff _ _ _).2 ((h _ hg1 _ hg2 z).2 ⟨rfl, rfl⟩).symm },
        { simp only [hg2, prob_output_eq_zero, not_false_iff, zero_mul] } } },
    { simp only [prob_output_eq_zero hg1, zero_mul] } }
end

end oracle_comp