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

variables {α β γ : Type} {spec spec' : oracle_spec}

-- TODO: `prod` -> `oracle_prod`
def oracle_comp.prod (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  oracle_comp spec (α × β) := do {a ← oa, b ← ob, return (a, b)}

infixr `×ₘ` : 100 := oracle_comp.prod

namespace oracle_comp

open oracle_spec
open_locale ennreal big_operators

lemma prod_def (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  oa ×ₘ ob = do {a ← oa, b ← ob, return (a, b)} := rfl

section support



end support

section fin_support



end fin_support

section distribution_semantics

open distribution_semantics

variable [spec.finite_range]

section eval_dist

/-- Since the two computations run independently, the probability of an element
  is the product of the two individual probabilities-/
@[simp] lemma eval_dist_prod_apply (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (x : α × β) : ⦃oa ×ₘ ob⦄ x = ⦃oa⦄ x.1 * ⦃ob⦄ x.2 :=
calc ⦃oa ×ₘ ob⦄ x = ∑' (a : α) (b : β), (⦃oa⦄ a * ⦃ob⦄ b) * (⦃return (a, b)⦄ x) :
    by simp_rw [prod_def, eval_dist_bind_apply_eq_tsum, ← ennreal.tsum_mul_left, mul_assoc]
  ... = ∑' (y : α × β), (⦃oa⦄ y.1 * ⦃ob⦄ y.2) * (⦃(return (y.1, y.2) : oracle_comp spec _)⦄ x) :
    by rw ← ennreal.tsum_prod
  ... = (⦃oa⦄ x.1 * ⦃ob⦄ x.2) * (⦃(return (x.1, x.2) : oracle_comp spec _)⦄ x) :
    tsum_eq_single x (λ y hy, by rw [prod.mk.eta, eval_dist_return_apply_of_ne hy.symm, mul_zero])
  ... = ⦃oa⦄ x.1 * ⦃ob⦄ x.2 : by rw [prod.mk.eta, eval_dist_return_apply_self, mul_one]

@[simp] lemma eval_dist_indicator_prod_apply (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (e : set α) (e' : set β) (a : α) (b : β) :
  (e ×ˢ e').indicator ⦃oa ×ₘ ob⦄ (a, b) = (e.indicator ⦃oa⦄ a) * (e'.indicator ⦃ob⦄ b) :=
begin
  by_cases ha : a ∈ e,
  { by_cases hb : b ∈ e',
    { have : (a, b) ∈ (e ×ˢ e') := ⟨ha, hb⟩,
      rw [set.indicator_apply_eq_self.2 (λ h, (h this).elim),
        set.indicator_apply_eq_self.2 (λ h, (h ha).elim),
        set.indicator_apply_eq_self.2 (λ h, (h hb).elim), eval_dist_prod_apply] },
    { have : (a, b) ∉ (e ×ˢ e') := λ h, hb h.2,
      rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
        set.indicator_apply_eq_zero.2 (λ h, (hb h).elim), mul_zero] } },
  { have : (a, b) ∉ (e ×ˢ e') := λ h, ha h.1,
    rw [set.indicator_apply_eq_zero.2 (λ h, (this h).elim),
      set.indicator_apply_eq_zero.2 (λ h, (ha h).elim), zero_mul] }
end

end eval_dist

section prob_event

lemma prob_event_set_prod_eq_mul
  (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (e : set α) (e' : set β) : ⦃e ×ˢ e' | oa ×ₘ ob⦄ = ⦃e | oa⦄ * ⦃e' | ob⦄ :=
calc ⦃e ×ˢ e' | oa ×ₘ ob⦄
  = ∑' (x : α × β), (e ×ˢ e').indicator (⦃oa ×ₘ ob⦄) x : (prob_event_eq_tsum_indicator _ _)
  ... = (∑' a, e.indicator ⦃oa⦄ a) * (∑' b, e'.indicator ⦃ob⦄ b) :
  begin
    simp_rw [← ennreal.tsum_mul_right, ← ennreal.tsum_mul_left,
      tsum_prod' ennreal.summable (λ _, ennreal.summable)],
    refine tsum_congr (λ a, tsum_congr (λ b, eval_dist_indicator_prod_apply oa ob e e' a b)),
  end
  ... = ⦃e | oa⦄ * ⦃e' | ob⦄ : by simp_rw [prob_event_eq_tsum_indicator]

end prob_event

-- section indep_events

-- /-- Any collections of sets corresponding to output types of two computations
--   are independent when returning the outputs of the computations in a `prod` type -/
-- lemma indep_events_prod (oa : oracle_comp spec α) (ob : oracle_comp spec β)
--   (events₁ : set (set α)) (events₂ : set (set β)) :
--   indep_events (oa ×ₘ ob) ((λ e, {x | x.1 ∈ e}) '' events₁) ((λ e, {x | x.2 ∈ e}) '' events₂) :=
-- sorry

-- end indep_events

-- section indep_event

-- /-- Any events corresponding to two computations respective output types
--   are independent when returning the two outputs in a `prod` type -/
-- lemma indep_event_prod (e₁ : set α) (e₂ : set β)
--   (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
--   indep_event (oa ×ₘ ob) {x | x.1 ∈ e₁} {x | x.2 ∈ e₂} :=
-- sorry

-- end indep_event

end distribution_semantics

end oracle_comp