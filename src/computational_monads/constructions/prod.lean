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

infixl `×ₘ` : 100 := oracle_comp.prod

namespace oracle_comp

open oracle_spec

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

@[simp]
lemma eval_dist_prod_apply
  (oa : oracle_comp spec α) (ob : oracle_comp spec β) (a : α) (b : β) :
  ⦃oa ×ₘ ob⦄ (a, b) = ⦃oa⦄ a * ⦃ob⦄ b :=
calc ⦃oa ×ₘ ob⦄ (a, b) = ∑' (x : α) (y : β), (⦃oa⦄ x * ⦃ob⦄ y) * (⦃return (x, y)⦄ (a, b)) :
    by simp_rw [prod_def, eval_dist_bind_apply_eq_tsum, ← ennreal.tsum_mul_left, mul_assoc]
  ... = (⦃oa⦄ a * ⦃ob⦄ b) * (⦃(return (a, b) : oracle_comp spec _)⦄ (a, b)) :
    begin
      refine tsum_tsum_eq_single _ a b (λ a' ha', _) (λ a' b' hb', _),
      { have : (a, b) ≠ (a', b) := λ h, ha' (prod.eq_iff_fst_eq_snd_eq.1 h).1.symm,
        simp only [eval_dist_return_apply_of_ne this, if_false, mul_zero]},
      { have : (a, b) ≠ (a', b') := λ h, hb' (prod.eq_iff_fst_eq_snd_eq.1 h).2.symm,
        simp only [eval_dist_return_apply_of_ne this, if_false, mul_zero]}
    end
  ... = ⦃oa⦄ a * ⦃ob⦄ b : by rw [eval_dist_return_apply_self, mul_one]

end eval_dist

section prob_event

lemma prob_event_set_prod_eq_mul
  (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (e : set α) (e' : set β) [decidable_pred e] [decidable_pred e'] :
  ⦃e ×ˢ e' | oa ×ₘ ob⦄ = ⦃e | oa⦄ * ⦃e' | ob⦄ :=
calc ⦃e ×ˢ e' | oa ×ₘ ob⦄
  = ∑' (x : α × β), ite (x ∈ e ×ˢ e') (⦃oa⦄ x.1 * ⦃ob⦄ x.2) 0 :
  begin
    refine trans (prob_event_eq_tsum_ite _ _) (tsum_congr (λ x, x.rec $ λ a b, _)),
    simp only [set.mem_prod, eval_dist_prod_apply, ← ennreal.coe_mul],
  end
  ... = (∑' a, ite (a ∈ e) (⦃oa⦄ a) 0) * (∑' b, ite (b ∈ e') (⦃ob⦄ b) 0) :
  begin
    simp_rw [← ennreal.tsum_mul_right, ← ennreal.tsum_mul_left,
      tsum_prod' ennreal.summable (λ _, ennreal.summable)],
    exact tsum_congr (λ a, tsum_congr (λ b, trans (by congr) (ite_and_mul_zero _ _ _ _))),
  end
  ... = ⦃e | oa⦄ * ⦃e' | ob⦄ : begin
    simp_rw [prob_event_eq_tsum_ite],
    congr;
    { ext x,
      split_ifs,
      refl, refl }
  end

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