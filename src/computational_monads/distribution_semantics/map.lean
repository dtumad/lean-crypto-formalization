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
  support_map, coe_fin_support]

lemma mem_fin_support_map_iff [decidable_eq α] [decidable_eq β] :
  y ∈ (f <$> oa).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by rw [fin_support_map, finset.mem_image]

lemma apply_mem_support_map {oa : oracle_comp spec α} {x} (hx : x ∈ oa.support)
  (f : α → β) : f x ∈ (f <$> oa).support :=
have ∃ (x' : α), x' ∈ oa.support ∧ f x' = f x := ⟨x, hx, rfl⟩,
  by simp only [this, support_map, set.mem_image]

end support

section eval_dist

@[simp] lemma eval_dist_map : ⁅f <$> oa⁆ = ⁅oa⁆.map f := eval_dist_bind oa (pure ∘ f)

end eval_dist

section prob_output

lemma prob_output_map_eq_tsum_ite [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑' x, if y = f x then ⁅= x | oa⁆ else 0 :=
prob_output_bind_return_eq_tsum oa f y

lemma prob_output_map_eq_tsum_indicator :
  ⁅= y | f <$> oa⁆ = ∑' x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
prob_output_bind_return_eq_tsum_indicator oa f y

lemma prob_output_map_eq_sum_ite [decidable_eq α] [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑ x in oa.fin_support, if y = f x then ⁅= x | oa⁆ else 0 :=
prob_output_bind_return_eq_sum_fin_support oa f y

lemma prob_output_map_eq_sum_indicator [decidable_eq α] :
  ⁅= y | f <$> oa⁆ = ∑ x in oa.fin_support, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
prob_output_bind_return_eq_sum_fin_support_indicator oa f y

lemma prob_output_map_eq_sum_fintype [fintype α] [decidable_eq β] :
  ⁅= y | f <$> oa⁆ = ∑ x, if y = f x then ⁅= x | oa⁆ else 0 :=
prob_output_bind_return_eq_sum oa f y

lemma prob_output_map_eq_sum_fintype_indicator [fintype α] :
  ⁅= y | f <$> oa⁆ = ∑ x, (f ⁻¹' {y}).indicator ⁅oa⁆ x :=
prob_output_bind_return_eq_sum_indicator oa f y

end prob_output

section prob_event

variable (p : β → Prop)

-- TODO!: we should either stick to predicates or sets probably? maybe not??
@[simp] lemma prob_event_map (p : β → Prop) : ⁅p | f <$> oa⁆ = ⁅p ∘ f | oa⁆ :=
prob_event_bind_return oa f p

@[simp] lemma prob_event_eq_eq_prob_output_map (y : β) (f : α → β) :
  ⁅λ x, f x = y | oa⁆ = ⁅= y | f <$> oa⁆ :=
by simp only [← prob_event_eq_eq_prob_output, prob_event_map, @eq_comm β _ y, set.preimage]

@[simp] lemma prob_event_eq_eq_prob_output_map' (y : β) (f : α → β) :
  ⁅λ x, y = f x | oa⁆ = ⁅= y | f <$> oa⁆ :=
by simp only [← prob_event_eq_eq_prob_output, prob_event_map]

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

-- lemma support_map_return : (f <$> (return' !spec! a)).support = {f a} :=
-- by rw [map_pure, support_pure]

-- lemma mem_support_map_return_iff : y ∈ (f <$> (return' !spec! a)).support ↔ y = f a :=
-- by rw [map_pure, mem_support_return_iff]

-- lemma fin_support_map_return [decidable_eq β] : (f <$> return' !spec! a).fin_support = {f a} :=
-- by rw [map_pure, fin_support_return]

-- lemma mem_fin_support_map_return_iff [decidable_eq β] :
--   y ∈ (f <$> return' !spec! a).fin_support ↔ y = f a :=
-- by rw [map_pure, mem_fin_support_return_iff]

-- lemma eval_dist_map_return : ⁅f <$> return' !spec! a⁆ = pmf.pure (f a) :=
-- by rw [map_pure, eval_dist_return]

-- lemma prob_output_map_return (x : β) :
--   ⁅= x | f <$> return' !spec! a⁆ = ⁅= x | return' !spec! (f a)⁆ :=
-- by pairwise_dist_equiv

-- lemma prob_event_map_return (q : set β) :
--   ⁅e | f <$> (return' !spec! a)⁆ = ⁅e | return' !spec! (f a)⁆ :=
-- by rw [map_pure]

end map_return

section map_comp

@[pairwise_dist_equiv] lemma map_comp_dist_equiv : g <$> (f <$> oa) ≃ₚ (g ∘ f) <$> oa :=
by simp only [map_map_eq_map_comp]

-- lemma support_map_comp : (g <$> (f <$> oa)).support = ((g ∘ f) <$> oa).support :=
-- by rw [map_map_eq_map_comp]

-- lemma fin_support_map_comp [decidable_eq γ] :
--   (g <$> (f <$> oa)).fin_support = ((g ∘ f) <$> oa).fin_support :=
-- by pairwise_dist_equiv

-- lemma eval_dist_map_comp : ⁅g <$> (f <$> oa)⁆ = ⁅oa⁆.map (g ∘ f) :=
-- by simp only [eval_dist_map, pmf.map_comp]

-- lemma prob_output_map_comp (x : γ) : ⁅= x | g <$> (f <$> oa)⁆ = ⁅= x | (g ∘ f) <$> oa⁆ :=
-- by pairwise_dist_equiv

-- lemma prob_event_map_comp (p : set γ) : ⁅e | g <$> (f <$> oa)⁆ = ⁅e | (g ∘ f) <$> oa⁆ :=
-- by pairwise_dist_equiv

end map_comp

section map_bind

@[simp] protected lemma map_bind : g <$> (oa >>= ob) = oa >>= λ x, g <$> (ob x) :=
by rw [map_bind]

-- lemma support_map_bind : (g <$> (oa >>= ob)).support =
--   ⋃ a ∈ oa.support, g '' (ob a).support :=
-- by simp [support_map, support_bind, set.image_Union]

-- lemma mem_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).support ↔
--   ∃ x ∈ oa.support, ∃ y ∈ (ob x).support, g y = z :=
-- by simp only [support_map_bind, set.mem_Union, set.mem_image, exists_prop]

-- lemma fin_support_map_bind [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
--   (g <$> (oa >>= ob)).fin_support =
--     finset.bUnion oa.fin_support (λ a, (ob a).fin_support.image g) :=
-- by simp only [map_bind, fin_support_bind, fin_support_map]

-- lemma mem_fin_support_map_bind_iff [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
--   z ∈ (g <$> (oa >>= ob)).fin_support ↔
--     ∃ x ∈ oa.fin_support, ∃ y ∈ (ob x).fin_support, g y = z :=
-- by simp only [fin_support_map_bind, finset.mem_bUnion, finset.mem_image]

-- @[pairwise_dist_equiv] lemma map_bind_dist_equiv : g <$> (oa >>= ob) ≃ₚ oa >>= (λ x, g <$> ob x) :=
-- by simp only [dist_equiv.def, eval_dist_map, eval_dist_bind, pmf.map_bind]

-- lemma eval_dist_map_bind : ⁅g <$> (oa >>= ob)⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆.map g) :=
-- by simp only [eval_dist_map, eval_dist_bind, pmf.map_bind]

-- lemma eval_dist_map_bind' : ⁅g <$> (oa >>= ob)⁆ = ⁅oa >>= (λ x, g <$> (ob x))⁆ :=
-- by pairwise_dist_equiv

-- lemma prob_output_map_bind_eq_tsum [decidable_eq γ] :
--   ⁅= z | g <$> (oa >>= ob)⁆ = ∑' (x : α) (y : β), ⁅= x | oa⁆ * (ite (z = g y) (⁅= y | ob x⁆) 0) :=
-- begin
--   rw [map_bind, prob_output_bind_eq_tsum],
--   simp only [prob_output_map_eq_tsum_ite, ennreal.tsum_mul_left],
-- end

-- lemma prob_output_map_bind_eq_sum [fintype α] [fintype β] [decidable_eq γ] :
--   ⁅= z | g <$> (oa >>= ob)⁆ = ∑ (x : α) (y : β), ⁅= x | oa⁆ * (ite (z = g y) ⁅= y | ob x⁆ 0) :=
-- by simp only [prob_output_map_bind_eq_tsum, tsum_fintype]

-- lemma prob_output_map_bind_eq_sum_fin_support [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
--   ⁅= z | g <$> (oa >>= ob)⁆ = ∑ x in oa.fin_support,
--     ∑ y in (ob x).fin_support, ⁅= x | oa⁆ * (ite (z = g y) ⁅= y | ob x⁆ 0) :=
-- by simp only [map_bind, prob_output_bind_eq_sum, prob_output_map_eq_sum_ite, finset.mul_sum]
-- -- trans ((map_bind_dist_equiv _ _ _).prob_output_eq _) (by simp only
-- --   [prob_output_bind_eq_sum_fin_support, prob_output_map_eq_sum_fin_support, finset.mul_sum])

-- lemma prob_event_map_bind (e' : set γ) :
--   ⁅e' | g <$> (oa >>= ob)⁆ = ⁅e' | oa >>= λ x, g <$> (ob x)⁆ :=
-- by pairwise_dist_equiv

lemma map_bind_dist_equiv_left (f : β → α) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : ∀ x ∈ oa.support, f '' (ob x).support = {x}) : f <$> (oa >>= ob) ≃ₚ oa :=
begin
  rw [map_bind],
  refine bind_dist_equiv_left _ _ (λ x hx, _),
  rw [dist_equiv_return_iff', support_map, h x hx],
end

lemma map_bind_dist_equiv_right {f : β → γ} {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  (x : α) (h : ∀ y ∈ oa.support, f <$> ob y ≃ₚ f <$> ob x) :
  f <$> (oa >>= ob) ≃ₚ f <$> (ob x) :=
by simpa only [map_bind] using bind_dist_equiv_right _ _ _ h

end map_bind

section bind_map

-- TODO: precedence of simp might make this an ok simp lemma
-- the inner map would still attempt to simplify first
protected lemma bind_map : (f <$> oa) >>= oc = oa >>= oc ∘ f :=
by simp_rw [map_eq_bind_pure_comp, bind_assoc, pure_bind]

-- lemma bind_map_dist_equiv : (f <$> oa) >>= oc ≃ₚ oa >>= oc ∘ f :=
-- by simp only [dist_equiv.def, eval_dist_bind, eval_dist_map, pmf.bind_map]

-- lemma support_bind_map : ((f <$> oa) >>= oc).support =
--   ⋃ x ∈ oa.support, (oc (f x)).support :=
-- by simp only [support_bind, support_map, set.mem_image,
--   set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

-- lemma mem_support_bind_map_iff : z ∈ ((f <$> oa) >>= oc).support ↔
--   ∃ x ∈ oa.support, z ∈ (oc (f x)).support :=
-- by simp only [support_bind, set.mem_Union, support_map, set.mem_image,
--   set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

-- @[simp] lemma fin_support_bind_map [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
--   ((f <$> oa) >>= oc).fin_support =
--     finset.bUnion oa.fin_support (λ a, (oc (f a)).fin_support) :=
-- by simp [oracle_comp.bind_map] 

-- lemma mem_fin_support_bind_map_iff [decidable_eq α] [decidable_eq β] [decidable_eq γ] :
--   z ∈ ((f <$> oa) >>= oc).fin_support ↔ ∃ x ∈ oa.fin_support, z ∈ (oc (f x)).fin_support :=
-- by simp only [fin_support_bind_map, finset.mem_bUnion]

-- lemma eval_dist_bind_map : ⁅(f <$> oa) >>= oc⁆ = ⁅oa⁆.bind (λ y, ⁅oc (f y)⁆) :=
-- by simp only [eval_dist_bind, eval_dist_map, pmf.bind_map]

-- lemma eval_dist_bind_map' : ⁅(f <$> oa) >>= oc⁆ = ⁅oa >>= oc ∘ f⁆ :=
-- by pairwise_dist_equiv [bind_map_dist_equiv]

-- lemma prob_output_bind_map_eq_tsum : ⁅= z | (f <$> oa) >>= oc⁆ =
--   ∑' (x : α), ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
-- trans ((bind_map_dist_equiv _ _ _).prob_output_eq z) (prob_output_bind_eq_tsum _ _ _)

-- lemma prob_output_bind_map_eq_sum [fintype α] : ⁅= z | (f <$> oa) >>= oc⁆ =
--   ∑ (x : α), ⁅oa⁆ x * ⁅oc (f x)⁆ z :=
-- by rw [oracle_comp.bind_map, prob_output_bind_eq_sum_fintype]; refl
-- -- trans ((bind_map_dist_equiv _ _ _).prob_output_eq z) (prob_output_bind_eq_sum _ _ _)

-- lemma prob_output_bind_map_eq_sum_fin_support [decidable_eq α] [decidable_eq γ] :
--   ⁅= z | (f <$> oa) >>= oc⁆ =
--     ∑ x in oa.fin_support, ⁅= x | oa⁆ * ⁅= z | oc (f x)⁆ :=
-- trans ((bind_map_dist_equiv _ _ _).prob_output_eq z) (prob_output_bind_eq_sum_fin_support _ _ _)

end bind_map

section map_const

variables (b : β)

@[pairwise_dist_equiv]
lemma map_const_dist_equiv' : (λ _, b) <$> oa ≃ₚ return' !spec'! b :=
(bind_const_dist_equiv oa (return b)).trans (return_dist_equiv_return spec spec' b)

@[simp_dist_equiv]
lemma map_const_dist_equiv : (λ _, b) <$> oa ≃ₚ return' !spec! b :=
bind_const_dist_equiv oa (return b)

@[simp] lemma map_const_dist_equiv_iff (ob : oracle_comp spec β) :
  (λ _, b) <$> oa ≃ₚ ob ↔ (return' !spec! b) ≃ₚ ob :=
⟨λ h, trans (map_const_dist_equiv oa b).symm h, λ h, trans (map_const_dist_equiv oa b) h⟩

@[simp] lemma dist_equiv_const_map_iff (ob : oracle_comp spec β) :
  ob ≃ₚ (λ _, b) <$> oa ↔ ob ≃ₚ (return' !spec! b) :=
dist_equiv.symm_iff.trans (trans (map_const_dist_equiv_iff oa b ob) dist_equiv.symm_iff)

@[simp] lemma support_map_const : ((λ _, b) <$> oa).support = {b} :=
by simp only [map_eq_bind_pure_comp, function.comp_const, support_bind_const, support_return]

@[simp] lemma fin_support_map_const [decidable_eq β] : ((λ _, b) <$> oa).fin_support = {b} :=
by simp only [fin_support_eq_iff_support_eq_coe, support_map_const, finset.coe_singleton]

@[simp] lemma eval_dist_map_const : ⁅(λ _, b) <$> oa⁆ = pmf.pure b :=
by simp only [eval_dist_map, pmf.map_const]

@[simp] lemma prob_output_map_const (y : β) : ⁅= y | (λ _, b) <$> oa⁆ = ⁅= y | return' !spec! b⁆ :=
by pairwise_dist_equiv [map_const_dist_equiv']

@[simp] lemma prob_event_map_const (p : β → Prop) :
  ⁅p | (λ _, b) <$> oa⁆ = ⁅p | return' !spec! b⁆ :=
by pairwise_dist_equiv [map_const_dist_equiv']

end map_const

section eq_single

variables {f y}

lemma prob_output_map_eq_single' (hx : f x = y) (h : ∀ x' ∈ oa.support, f x' = y → x' = x) :
  ⁅= y | f <$> oa⁆ = ⁅= x | oa⁆ := prob_output_bind_return_eq_single' oa f y x hx h

/-- If a function `f` returns `y` iff the input is `x`, then the probability of outputting
`y` after running a computation and applying `f` is the probability of outputting `x`-/
lemma prob_output_map_eq_single (hx : f ⁻¹' {y} = {x}) :
  ⁅= y | f <$> oa⁆ = ⁅= x | oa⁆ := prob_output_bind_return_eq_single oa f y x hx

lemma prob_output_map_of_injective (hf : f.injective) : ⁅= f x | f <$> oa⁆ = ⁅= x | oa⁆ :=
prob_output_map_eq_single' oa x rfl (λ x' hx' hxf, hf hxf)

end eq_single

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

-- TODO: actual place for this
@[simp] lemma prob_output_map_to_list {n : ℕ} (xs : list α) (oa : oracle_comp spec (vector α n)) :
  ⁅= xs | vector.to_list <$> oa⁆ = if h : xs.length = n then ⁅= ⟨xs, h⟩ | oa⁆ else 0 :=
begin
  split_ifs with h,
  { exact (prob_output_map_of_injective oa ⟨xs, h⟩ vector.to_list_injective) },
  { simp_rw [prob_output_eq_zero_iff, support_map, set.mem_image, not_exists, not_and_distrib],
    refine λ xs', or.inr (λ hxs', h (hxs' ▸ xs'.to_list_length)) }
end

end oracle_comp