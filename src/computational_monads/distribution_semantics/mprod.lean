/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.push_map_dist_equiv
import to_mathlib.mprod

/-!
# Distribution Semantics of Monadic Product

This file contains lemmas about the distributions associated to the monadic product operation,
which takes two different computations, runs them independently, and returns them as a pair.

We show that the support is set product of the two individual supports,
and that the probability of an output is the product of the individual probabilities for each
component (in particular the two outputs are independent)
-/

namespace oracle_comp

open oracle_spec prod
open_locale ennreal big_operators

variables {α β γ δ : Type} {spec spec' : oracle_spec}

variables (oa oa' : oracle_comp spec α) (ob ob' : oracle_comp spec β)
  (e : set α) (e' : set β) (a : α) (b : β) (x : α × β)

lemma mprod_dist_equiv : (oa ×ₘ ob) ≃ₚ do {a ← oa, b ← ob, return (a, b)} := refl _

section support

@[simp] lemma support_mprod : (oa ×ₘ ob).support = oa.support ×ˢ ob.support :=
set.ext (λ x, by simp only [mprod.def, eq_iff_fst_eq_snd_eq, support_bind, support_bind_return,
  set.mem_Union, set.mem_image, exists_eq_right_right, exists_prop, set.mem_prod])

lemma mem_support_mprod_iff : x ∈ (oa ×ₘ ob).support ↔ x.1 ∈ oa.support ∧ x.2 ∈ ob.support :=
by rw [support_mprod, set.mem_prod]

end support

section fin_support

variables [decidable_eq α] [decidable_eq β]

@[simp] lemma fin_support_mprod : (oa ×ₘ ob).fin_support = oa.fin_support ×ˢ ob.fin_support :=
by simp only [fin_support_eq_iff_support_eq_coe, support_mprod,
  finset.coe_product, coe_fin_support_eq_support]

lemma mem_fin_support_mprod_iff : x ∈ (oa ×ₘ ob).fin_support ↔
  x.1 ∈ oa.fin_support ∧ x.2 ∈ ob.fin_support :=
by rw [fin_support_mprod, finset.mem_product]

end fin_support

section prob_output

/-- Since the two computations run independently, the probability of an element
  is the product of the two individual probabilities -/
@[simp] lemma prob_output_mprod : ⁅= x | oa ×ₘ ob⁆ = ⁅= x.1 | oa⁆ * ⁅= x.2 | ob⁆ :=
calc ⁅= x | oa ×ₘ ob⁆ = ∑' a b, (⁅= a | oa⁆ * ⁅= b | ob⁆) * ⁅= x | return' !spec! (a, b)⁆ :
    by simp_rw [mprod.def, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left, mul_assoc]
  ... = ∑' (y : α × β), (⁅= y.1 | oa⁆ * ⁅= y.2 | ob⁆) * ⁅= x | return' !spec! (y.1, y.2)⁆ :
    by rw ← ennreal.tsum_prod
  ... = (⁅= x.1 | oa⁆ * ⁅= x.2 | ob⁆) * ⁅= x | return' !spec! (x.1, x.2)⁆ :
    tsum_eq_single x (λ y hy, by rw [mk.eta, prob_output_return_of_ne _ hy.symm, mul_zero])
  ... = ⁅= x.1 | oa⁆ * ⁅= x.2 | ob⁆ : by rw [mk.eta, prob_output_return_self, mul_one]

end prob_output

section dist_equiv

lemma mprod_dist_equiv_mprod {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  {ob : oracle_comp spec β} {ob' : oracle_comp spec' β}
  (ha : oa ≃ₚ oa') (hb : ob ≃ₚ ob') : (oa ×ₘ ob) ≃ₚ (oa' ×ₘ ob') :=
bind_dist_equiv_bind_of_dist_equiv ha (λ x _,
  bind_dist_equiv_bind_of_dist_equiv hb (λ y _, return_dist_equiv_return _ _ _))

@[pairwise_dist_equiv] lemma mprod_bind_equiv_bind_bind (oc : α × β → oracle_comp spec γ) :
  (oa ×ₘ ob) >>= oc ≃ₚ do {a ← oa, b ← ob, oc (a, b)} :=
dist_equiv.ext (λ x, by simp only [prob_output_bind_eq_tsum, prob_output_mprod,
  ← ennreal.tsum_mul_left, ← ennreal.tsum_prod, mk.eta, mul_assoc])

end dist_equiv

section eval_dist

@[simp] lemma eval_dist_mprod_indicator_prod_apply :
  (e ×ˢ e').indicator ⁅oa ×ₘ ob⁆ x = (e.indicator ⁅oa⁆ x.1) * (e'.indicator ⁅ob⁆ x.2) :=
begin
  by_cases ha : x.1 ∈ e,
  { by_cases hb : x.2 ∈ e',
    { have : x ∈ (e ×ˢ e') := ⟨ha, hb⟩,
      simp [set.indicator_apply_eq_self.2 (λ h, (h this).elim),
        set.indicator_apply_eq_self.2 (λ h, (h ha).elim),
        set.indicator_apply_eq_self.2 (λ h, (h hb).elim), prob_output_mprod] },
    { have : x ∉ (e ×ˢ e') := λ h, hb h.2,
      rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
        set.indicator_apply_eq_zero.2 (λ h, (hb h).elim), mul_zero] } },
  { have : x ∉ (e ×ˢ e') := λ h, ha h.1,
    rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
      set.indicator_apply_eq_zero.2 (λ h, (ha h).elim), zero_mul] }
end

lemma eval_dist_mprod_indicator_preimage_fst_apply :
  (fst ⁻¹' e).indicator ⁅oa ×ₘ ob⁆ (a, b) = e.indicator ⁅oa⁆ a * ⁅ob⁆ b :=
begin
  by_cases ha : a ∈ e,
  { have : (a, b) ∈ (fst ⁻¹' e : set (α × β)) := set.mem_preimage.2 ha,
    simp [set.indicator_apply_eq_self.2 (λ h, (h this).elim),
      set.indicator_apply_eq_self.2 (λ h, (h ha).elim), prob_output_mprod] },
  { have : (a, b) ∉ (fst ⁻¹' e : set (α × β)) := λ h, ha (set.mem_preimage.2 h),
    rw [set.indicator_apply_eq_zero.2 (λ  h, (this h).elim),
      set.indicator_apply_eq_zero.2 (λ h, (ha h).elim), zero_mul] }
end

lemma eval_dist_mprod_indicator_preimage_snd_apply :
  (snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b) = ⁅oa⁆ a * e'.indicator ⁅ob⁆ b :=
begin
  by_cases hb : b ∈ e',
  { have : (a, b) ∈ (snd ⁻¹' e' : set (α × β)) := set.mem_preimage.2 hb,
    simp [set.indicator_apply_eq_self.2 (λ h, (h this).elim),
      set.indicator_apply_eq_self.2 (λ h, (h hb).elim), prob_output_mprod] },
  { have : (a, b) ∉ (snd ⁻¹' e' : set (α × β)) := λ h, hb (set.mem_preimage.2 h),
    rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
      set.indicator_apply_eq_zero.2 (λ h, (hb h).elim), mul_zero] }
end

@[pairwise_dist_equiv] lemma map_mprod_dist_equiv (f : α × β → γ) :
  f <$> (oa ×ₘ ob) ≃ₚ do {x ← oa, y ← ob, return (f (x, y))} :=
by pairwise_dist_equiv

@[pairwise_dist_equiv] lemma fst_map_mprod_dist_equiv :
  fst <$> (oa ×ₘ ob) ≃ₚ oa :=
begin
  refine trans (map_mprod_dist_equiv oa ob fst) _,
  simp only [],
  rw_dist_equiv [bind_const_dist_equiv, bind_return_id_dist_equiv],
end

@[pairwise_dist_equiv] lemma snd_map_mprod_dist_equiv :
  snd <$> (oa ×ₘ ob) ≃ₚ ob :=
begin
  refine trans (map_mprod_dist_equiv oa ob snd) _,
  simp only [],
  rw_dist_equiv [bind_const_dist_equiv, bind_return_id_dist_equiv],
end

@[pairwise_dist_equiv] lemma map_prod_mprod_dist_equiv (f : α → γ) (g : β → δ) :
  map f g <$> (oa ×ₘ ob) ≃ₚ ((f <$> oa) ×ₘ (g <$> ob)) :=
by rw_dist_equiv [map_bind_dist_equiv, map_bind_dist_equiv, bind_map_dist_equiv,
  bind_map_dist_equiv, map_return_dist_equiv]

lemma prob_output_map_fst_mprod [decidable_eq γ] (f : α × β → γ) (x : α × γ) :
  ⁅= x | (λ (x : α × β), (fst x, f x)) <$> (oa ×ₘ ob)⁆ =
    ∑' (b : β), if x.2 = f (x.1, b) then ⁅= x.1 | oa⁆ * ⁅= b | ob⁆ else 0 :=
begin
  simp only [prob_output.def, eval_dist_map, pmf.map_apply, ennreal.tsum_prod'],
  refine trans ennreal.tsum_comm (tsum_congr (λ b, (tsum_eq_single x.1 (λ b' hb', _)).trans _)),
  { simp [hb'.symm, eq_iff_fst_eq_snd_eq] },
  { simp [eq_iff_fst_eq_snd_eq] }
end

lemma prob_output_map_snd_mprod [decidable_eq γ] (f : α × β → γ) (x : γ × β) :
  ⁅= x | (λ (x : α × β), (f x, snd x)) <$> (oa ×ₘ ob)⁆ =
    ∑' (a : α), if x.1 = f (a, x.2) then ⁅= a | oa⁆ * ⁅= x.2 | ob⁆ else 0 :=
begin
  simp only [prob_output.def, eval_dist_map, pmf.map_apply, ennreal.tsum_prod'],
  refine tsum_congr (λ a, (tsum_eq_single x.2 (λ a' ha', _)).trans _),
  { simp [ha'.symm, eq_iff_fst_eq_snd_eq] },
  { simp [eq_iff_fst_eq_snd_eq] }
end

end eval_dist

section prob_event

@[simp] lemma prob_event_mprod_eq_mul : ⁅e ×ˢ e' | oa ×ₘ ob⁆ = ⁅e | oa⁆ * ⁅e' | ob⁆ :=
calc ⁅e ×ˢ e' | oa ×ₘ ob⁆ = ∑' x, (e ×ˢ e').indicator ⁅oa ×ₘ ob⁆ x :
    (prob_event_eq_tsum_indicator _ _)
  ... = ∑' (x : α × β), e.indicator ⁅oa⁆ x.1 * e'.indicator ⇑⁅ob⁆ x.2 :
    tsum_congr (λ x, eval_dist_mprod_indicator_prod_apply oa ob e e' x)
  ... = (∑' a, e.indicator ⁅oa⁆ a) * (∑' b, e'.indicator ⁅ob⁆ b) :
    by simp_rw [← ennreal.tsum_mul_right, ← ennreal.tsum_mul_left, ← ennreal.tsum_prod]
  ... = ⁅e | oa⁆ * ⁅e' | ob⁆ : by simp_rw [prob_event_eq_tsum_indicator]

/-- If an event only cares about the first part of the computation,
we can calculate the probability using only the first of the computations. -/
@[simp] lemma prob_event_mprod_preimage_fst : ⁅fst ⁻¹' e | oa ×ₘ ob⁆ = ⁅e | oa⁆ :=
calc ⁅fst ⁻¹' e | oa ×ₘ ob⁆
  = ∑' (x : α × β), (fst ⁻¹' e).indicator ⇑⁅oa×ₘ ob⁆ (x.1, x.2) :
    by simp_rw [prob_event_eq_tsum_indicator, mk.eta]
  ... = ∑' a b, (fst ⁻¹' e).indicator ⇑⁅oa×ₘ ob⁆ (a, b) :
    @ennreal.tsum_prod α β (λ a b, (fst ⁻¹' e).indicator ⇑⁅oa×ₘ ob⁆ (a, b))
  ... = ∑' a, e.indicator ⁅oa⁆ a : by simp only [eval_dist_mprod_indicator_preimage_fst_apply,
    ennreal.tsum_mul_left, ⁅ob⁆.tsum_coe, mul_one]
  ... = ⁅e | oa⁆ : by rw [prob_event_eq_tsum_indicator]

/-- If an event only cares about the second part of the computation,
we can calculate the probability using only the first of the computations. -/
lemma prob_event_mprod_preimage_snd : ⁅snd ⁻¹' e' | oa ×ₘ ob⁆ = ⁅e' | ob⁆ :=
calc ⁅snd ⁻¹' e' | oa ×ₘ ob⁆
  = ∑' (x : α × β), (snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (x.1, x.2) :
    by simp_rw [prob_event_eq_tsum_indicator, mk.eta]
  ... = ∑' a b, (snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b) :
    @ennreal.tsum_prod α β (λ a b, (snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b))
  ... = ∑' b a, (snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b) : ennreal.tsum_comm
  ... = ∑' b, e'.indicator ⁅ob⁆ b : by simp only [eval_dist_mprod_indicator_preimage_snd_apply,
    ennreal.tsum_mul_right, ⁅oa⁆.tsum_coe, one_mul]
  ... = ⁅e' | ob⁆ : by rw [prob_event_eq_tsum_indicator]

end prob_event

section indep_events

/-- Any collections of sets corresponding to output types of two computations
are independent when returning the outputs of the computations in a `prod` type. -/
lemma indep_events_prod (es : set (set α)) (es' : set (set β)) :
  indep_events (oa ×ₘ ob) ((λ e, fst ⁻¹' e) '' es) ((λ e', snd ⁻¹' e') '' es') :=
begin
  rw [indep_events_iff],
  intros e e' he he',
  obtain ⟨d, hd, hde⟩ := he,
  obtain ⟨d', hd', hde'⟩ := he',
  have hed : e = fst ⁻¹' d := hde.symm,
  have hed' : e' = snd ⁻¹' d' := hde'.symm,
  have h : e ∩ e' = d ×ˢ d',
  from set.ext (λ x, by simp only [hed, hed', set.mem_inter_iff, set.mem_preimage, set.mem_prod]),
  rw [h, hed, hed', prob_event_mprod_eq_mul, prob_event_mprod_preimage_fst,
    prob_event_mprod_preimage_snd],
end

/-- Any events corresponding to two computations respective output types
are independent when running the two independently and returning the two outputs in a `prod` type -/
lemma indep_event_prod (e : set α) (e' : set β) :
  indep_event (oa ×ₘ ob) (fst ⁻¹' e) (snd ⁻¹' e') :=
begin
  rw [indep_event_iff_indep_events],
  convert indep_events_prod oa ob {e} {e'};
  simp only [set.image_singleton],
end

end indep_events

section swap

lemma swap_map_dist_equiv : swap <$> (oa ×ₘ ob) ≃ₚ (ob ×ₘ oa) :=
by simp_rw_dist_equiv [map_bind_dist_equiv, map_return_dist_equiv, bind_bind_dist_equiv_comm]

end swap

section return

/-- if `oa ×ₘ ob ≃ₚ oc` then looking at just the first or second output the distribution
will look like that of `oa` and `ob` respectively. -/
lemma dist_equiv_map_fst_snd_of_mprod_dist_equiv (oc : oracle_comp spec' (α × β))
  (h : (oa ×ₘ ob) ≃ₚ oc) : (oa ≃ₚ fst <$> oc ∧ ob ≃ₚ snd <$> oc) :=
begin
  split,
  { refine trans _ (map_dist_equiv_of_dist_equiv' rfl h),
    simp [mprod.def, pmf.map_bind, pmf.map_comp] },
  { refine trans _ (map_dist_equiv_of_dist_equiv' rfl h),
    simp [mprod.def, pmf.map_bind, pmf.map_comp, pmf.map_id] }
end

/-- If the left computation is just a `return`, then `dist_equiv_map_fst_snd_of_mprod_dist_equiv`
can be written as an `iff` statement instead. -/
lemma return_mprod_dist_equiv_iff (oc : oracle_comp spec' (α × β)) :
  (return a ×ₘ ob) ≃ₚ oc ↔ ((return' !spec! a) ≃ₚ fst <$> oc) ∧ (ob ≃ₚ snd <$> oc) :=
begin
  refine ⟨λ h, dist_equiv_map_fst_snd_of_mprod_dist_equiv _ _ _ h, λ h, _⟩,
  rw_dist_equiv [return_bind_dist_equiv],
  refine trans (bind_dist_equiv_bind_of_dist_equiv h.2 (λ _ _, return_dist_equiv_return _ _ _)) _,
  rw_dist_equiv [bind_map_dist_equiv],
  refine bind_dist_equiv_left _ _ (λ z hz, _),
  have := apply_mem_support_map oc fst z hz,
  simp_rw [h.1.symm.support_eq, mem_support_return_iff] at this,
  exact return_dist_equiv_return_of_eq _ _ _ _ (eq_iff_fst_eq_snd_eq.2 ⟨this.symm, rfl⟩)
end

/-- If the right computation is just a `return`, then `dist_equiv_map_fst_snd_of_mprod_dist_equiv`
can be written as an `iff` statement instead. -/
lemma mprod_return_dist_equiv_iff (oc : oracle_comp spec' (α × β)) :
  (oa ×ₘ return b) ≃ₚ oc ↔ (oa ≃ₚ fst <$> oc) ∧ ((return' !spec! b) ≃ₚ snd <$> oc) :=
begin
  refine ⟨λ h, dist_equiv_map_fst_snd_of_mprod_dist_equiv _ _ _ h, λ h, _⟩,
  rw_dist_equiv [return_bind_dist_equiv],
  refine trans (bind_dist_equiv_bind_of_dist_equiv h.1 (λ _ _, return_dist_equiv_return _ _ _)) _,
  rw_dist_equiv [bind_map_dist_equiv],
  refine bind_dist_equiv_left _ _ (λ z hz, _),
  have := apply_mem_support_map oc snd z hz,
  simp_rw [h.2.symm.support_eq, mem_support_return_iff] at this,
  exact return_dist_equiv_return_of_eq _ _ _ _ (eq_iff_fst_eq_snd_eq.2 ⟨rfl, this.symm⟩)
end

end return

end oracle_comp