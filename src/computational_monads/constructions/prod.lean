/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.independence

/-!
# Pairwise Oracle Computations

This file defines a construction for running two computations,
returning both results together in a pair as a `prod` type.
`oa ×ₘ ob` represents the computation running both independently and returning both results.
-/

namespace oracle_comp

open oracle_spec
open_locale ennreal big_operators

variables {α β γ : Type} {spec spec' : oracle_spec}

-- TODO: `product`??
def prod (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  oracle_comp spec (α × β) := do {a ← oa, b ← ob, return (a, b)}

infixr `×ₘ` : 100 := oracle_comp.prod



variables (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (e : set α) (e' : set β) (a : α) (b : β) (x : α × β)

lemma prod.def : oa ×ₘ ob = do {a ← oa, b ← ob, return (a, b)} := rfl

instance prod.decidable [decidable_eq α] [decidable_eq β] [decidable oa] [decidable ob] :
  decidable (oa ×ₘ ob) := by {unfold prod, apply_instance}

section support

@[simp] lemma support_prod : (oa ×ₘ ob).support = oa.support ×ˢ ob.support :=
set.ext (λ x, by simp only [prod.def, prod.eq_iff_fst_eq_snd_eq, support_bind, support_bind_return,
  set.mem_Union, set.mem_image, exists_eq_right_right, exists_prop, set.mem_prod])

lemma mem_support_prod_iff : x ∈ (oa ×ₘ ob).support ↔ x.1 ∈ oa.support ∧ x.2 ∈ ob.support :=
by rw [support_prod, set.mem_prod]

end support

section fin_support

variables [decidable_eq α] [decidable_eq β] [decidable oa] [decidable ob]

@[simp] lemma fin_support_prod : (oa ×ₘ ob).fin_support = oa.fin_support ×ˢ ob.fin_support :=
by simp only [fin_support_eq_iff_support_eq_coe, support_prod,
  finset.coe_product, coe_fin_support_eq_support]

lemma mem_fin_support_prod_iff : x ∈ (oa ×ₘ ob).fin_support ↔
  x.1 ∈ oa.fin_support ∧ x.2 ∈ ob.fin_support :=
by rw [fin_support_prod, finset.mem_product]

end fin_support

section distribution_semantics

open distribution_semantics

section eval_dist

/-- Since the two computations run independently, the probability of an element
  is the product of the two individual probabilities-/
@[simp] lemma eval_dist_prod_apply : ⁅oa ×ₘ ob⁆ x = ⁅oa⁆ x.1 * ⁅ob⁆ x.2 :=
calc ⁅oa ×ₘ ob⁆ x = ∑' (a : α) (b : β), (⁅oa⁆ a * ⁅ob⁆ b) * (⁅return (a, b)⁆ x) :
    by simp_rw [prod.def, eval_dist_bind_apply_eq_tsum, ← ennreal.tsum_mul_left, mul_assoc]
  ... = ∑' (y : α × β), (⁅oa⁆ y.1 * ⁅ob⁆ y.2) * (⁅(return (y.1, y.2) : oracle_comp spec _)⁆ x) :
    by rw ← ennreal.tsum_prod
  ... = (⁅oa⁆ x.1 * ⁅ob⁆ x.2) * (⁅(return (x.1, x.2) : oracle_comp spec _)⁆ x) :
    tsum_eq_single x (λ y hy, by rw [prod.mk.eta, eval_dist_return_apply_of_ne hy.symm, mul_zero])
  ... = ⁅oa⁆ x.1 * ⁅ob⁆ x.2 : by rw [prod.mk.eta, eval_dist_return_apply_self, mul_one]

@[simp] lemma eval_dist_prod_indicator_prod_apply :
  (e ×ˢ e').indicator ⁅oa ×ₘ ob⁆ x = (e.indicator ⁅oa⁆ x.1) * (e'.indicator ⁅ob⁆ x.2) :=
begin
  by_cases ha : x.1 ∈ e,
  { by_cases hb : x.2 ∈ e',
    { have : x ∈ (e ×ˢ e') := ⟨ha, hb⟩,
      rw [set.indicator_apply_eq_self.2 (λ h, (h this).elim),
        set.indicator_apply_eq_self.2 (λ h, (h ha).elim),
        set.indicator_apply_eq_self.2 (λ h, (h hb).elim), eval_dist_prod_apply] },
    { have : x ∉ (e ×ˢ e') := λ h, hb h.2,
      rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
        set.indicator_apply_eq_zero.2 (λ h, (hb h).elim), mul_zero] } },
  { have : x ∉ (e ×ˢ e') := λ h, ha h.1,
    rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
      set.indicator_apply_eq_zero.2 (λ h, (ha h).elim), zero_mul] }
end

lemma eval_dist_prod_indicator_preimage_fst_apply :
  (prod.fst ⁻¹' e).indicator ⁅oa ×ₘ ob⁆ (a, b) = e.indicator ⁅oa⁆ a * ⁅ob⁆ b :=
begin
  by_cases ha : a ∈ e,
  { have : (a, b) ∈ (prod.fst ⁻¹' e : set (α × β)) := set.mem_preimage.2 ha,
    rw [set.indicator_apply_eq_self.2 (λ h, (h this).elim),
      set.indicator_apply_eq_self.2 (λ h, (h ha).elim), eval_dist_prod_apply] },
  { have : (a, b) ∉ (prod.fst ⁻¹' e : set (α × β)) := λ h, ha (set.mem_preimage.2 h),
    rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
      set.indicator_apply_eq_zero.2 (λ h, (ha h).elim), zero_mul] }
end

lemma eval_dist_prod_indicator_preimage_snd_apply :
  (prod.snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b) = ⁅oa⁆ a * e'.indicator ⁅ob⁆ b :=
begin
  by_cases hb : b ∈ e',
  { have : (a, b) ∈ (prod.snd ⁻¹' e' : set (α × β)) := set.mem_preimage.2 hb,
    rw [set.indicator_apply_eq_self.2 (λ h, (h this).elim),
      set.indicator_apply_eq_self.2 (λ h, (h hb).elim), eval_dist_prod_apply] },
  { have : (a, b) ∉ (prod.snd ⁻¹' e' : set (α × β)) := λ h, hb (set.mem_preimage.2 h),
    rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
      set.indicator_apply_eq_zero.2 (λ h, (hb h).elim), mul_zero] }
end

end eval_dist

section prob_event

@[simp] lemma prob_event_prod_eq_mul : ⁅e ×ˢ e' | oa ×ₘ ob⁆ = ⁅e | oa⁆ * ⁅e' | ob⁆ :=
calc ⁅e ×ˢ e' | oa ×ₘ ob⁆ = ∑' x, (e ×ˢ e').indicator ⁅oa ×ₘ ob⁆ x :
    (prob_event_eq_tsum_indicator _ _)
  ... = ∑' (x : α × β), e.indicator ⁅oa⁆ x.1 * e'.indicator ⇑⁅ob⁆ x.2 :
    tsum_congr (λ x, eval_dist_prod_indicator_prod_apply oa ob e e' x)
  ... = (∑' a, e.indicator ⁅oa⁆ a) * (∑' b, e'.indicator ⁅ob⁆ b) :
    by simp_rw [← ennreal.tsum_mul_right, ← ennreal.tsum_mul_left, ← ennreal.tsum_prod]
  ... = ⁅e | oa⁆ * ⁅e' | ob⁆ : by simp_rw [prob_event_eq_tsum_indicator]

/-- If an event only cares about the first part of the computation,
we can calculate the probability using only the first of the computations. -/
@[simp] lemma prob_event_prod_preimage_fst : ⁅prod.fst ⁻¹' e | oa ×ₘ ob⁆ = ⁅e | oa⁆ :=
calc ⁅prod.fst ⁻¹' e | oa ×ₘ ob⁆
  = ∑' (x : α × β), (prod.fst ⁻¹' e).indicator ⇑⁅oa×ₘ ob⁆ (x.1, x.2) :
    by simp_rw [prob_event_eq_tsum_indicator, prod.mk.eta]
  ... = ∑' a b, (prod.fst ⁻¹' e).indicator ⇑⁅oa×ₘ ob⁆ (a, b) :
    @ennreal.tsum_prod α β (λ a b, (prod.fst ⁻¹' e).indicator ⇑⁅oa×ₘ ob⁆ (a, b))
  ... = ∑' a, e.indicator ⁅oa⁆ a : by simp only [eval_dist_prod_indicator_preimage_fst_apply,
    ennreal.tsum_mul_left, ⁅ob⁆.tsum_coe, mul_one]
  ... = ⁅e | oa⁆ : by rw [prob_event_eq_tsum_indicator]

/-- If an event only cares about the second part of the computation,
we can calculate the probability using only the first of the computations. -/
lemma prob_event_prod_preimage_snd : ⁅prod.snd ⁻¹' e' | oa ×ₘ ob⁆ = ⁅e' | ob⁆ :=
calc ⁅prod.snd ⁻¹' e' | oa ×ₘ ob⁆
  = ∑' (x : α × β), (prod.snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (x.1, x.2) :
    by simp_rw [prob_event_eq_tsum_indicator, prod.mk.eta]
  ... = ∑' a b, (prod.snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b) :
    @ennreal.tsum_prod α β (λ a b, (prod.snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b))
  ... = ∑' b a, (prod.snd ⁻¹' e').indicator ⁅oa ×ₘ ob⁆ (a, b) : ennreal.tsum_comm
  ... = ∑' b, e'.indicator ⁅ob⁆ b : by simp only [eval_dist_prod_indicator_preimage_snd_apply,
    ennreal.tsum_mul_right, ⁅oa⁆.tsum_coe, one_mul]
  ... = ⁅e' | ob⁆ : by rw [prob_event_eq_tsum_indicator]

end prob_event

section indep_events

/-- Any collections of sets corresponding to output types of two computations
are independent when returning the outputs of the computations in a `prod` type. -/
theorem indep_events_prod (es : set (set α)) (es' : set (set β)) :
  indep_events (oa ×ₘ ob) ((λ e, prod.fst ⁻¹' e) '' es) ((λ e', prod.snd ⁻¹' e') '' es') :=
begin
  rw [indep_events_iff],
  intros e e' he he',
  obtain ⟨d, hd, hde⟩ := he,
  obtain ⟨d', hd', hde'⟩ := he',
  have hed : e = prod.fst ⁻¹' d := hde.symm,
  have hed' : e' = prod.snd ⁻¹' d' := hde'.symm,
  have h : e ∩ e' = d ×ˢ d',
  from set.ext (λ x, by simp only [hed, hed', set.mem_inter_iff, set.mem_preimage, set.mem_prod]),
  rw [h, hed, hed', prob_event_prod_eq_mul, prob_event_prod_preimage_fst,
    prob_event_prod_preimage_snd],
end

/-- Any events corresponding to two computations respective output types
are independent when running the two independently and returning the two outputs in a `prod` type -/
lemma indep_event_prod (e : set α) (e' : set β) :
  indep_event (oa ×ₘ ob) (prod.fst ⁻¹' e) (prod.snd ⁻¹' e') :=
begin
  rw [indep_event_iff_indep_events],
  convert indep_events_prod oa ob {e} {e'};
  simp only [set.image_singleton],
end

end indep_events

end distribution_semantics

end oracle_comp