import computational_monads.distribution_semantics.prob_event
import data.set.prod

/-! 
# Distributions Corresponding to Computations in Product Types

  -/

variables {spec spec' : oracle_spec} {α β γ : Type}
variable [spec.finite_range]

/-- TODO: Is this a useful thing to be using? -/
def oracle_prod (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  oracle_comp spec (α × β) := do {a ← oa, b ← ob, pure (a, b)}

infixl `×ₘ` : 100 := oracle_prod

namespace distribution_semantics

section eval_distribution

@[simp]
lemma eval_distribution_prod_apply [decidable_eq α] [decidable_eq β]
  (oa : oracle_comp spec α) (ob : oracle_comp spec β) (a : α) (b : β) :
  ⦃oa ×ₘ ob⦄ (a, b) = ⦃oa⦄ a * ⦃ob⦄ b :=
calc ⦃oa ×ₘ ob⦄ (a, b)
  = ∑' (x : α), ⦃oa⦄ x * ∑' (y : β), ⦃ob⦄ y * (if (a, b) = (x, y) then 1 else 0) :
    by simp_rw [oracle_prod, eval_distribution_bind_apply, eval_distribution_pure_apply]
  ... = ∑' (x : α) (y : β), (⦃oa⦄ x * ⦃ob⦄ y) * (if (a, b) = (x, y) then 1 else 0) :
    by simp_rw [← nnreal.tsum_mul_left, mul_assoc]
  ... = (⦃oa⦄ a * ⦃ob⦄ b) * (if (a, b) = (a, b) then 1 else 0) : begin
    refine tsum_tsum_eq_single _ a b (λ a' ha', _) (λ a' b' hb', _),
    { have : (a, b) ≠ (a', b) := λ h, ha' (prod.eq_iff_fst_eq_snd_eq.1 h).1.symm,
      simp [this] },
    { have : (a, b) ≠ (a', b') := λ h, hb' (prod.eq_iff_fst_eq_snd_eq.1 h).2.symm,
      simp [this] }
  end
  ... = ⦃oa⦄ a * ⦃ob⦄ b : by simp only [eq_self_iff_true, if_true, mul_one]

end eval_distribution

section prob_event

lemma prob_event_set_prod_eq_mul [decidable_eq α] [decidable_eq β]
  (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (e : set α) (e' : set β) [decidable_pred e] [decidable_pred e'] :
  ⦃e ×ˢ e' | oa ×ₘ ob⦄ = ⦃e | oa⦄ * ⦃e' | ob⦄ :=
calc ⦃e ×ˢ e' | oa ×ₘ ob⦄
  = ∑' (x : α × β), ite (x ∈ e ×ˢ e') (⦃oa⦄ x.1 * ⦃ob⦄ x.2) 0 : begin
    refine trans (prob_event_eq_tsum _ _) (tsum_congr (λ x, x.rec $ λ a b, _)),
    simp only [set.mem_prod, eval_distribution_prod_apply, ← ennreal.coe_mul],
  end
  ... = (∑' a, ite (a ∈ e) (⦃oa⦄ a) 0) * (∑' b, ite (b ∈ e') (⦃ob⦄ b) 0) :
  begin
    simp_rw [← ennreal.tsum_mul_right, ← ennreal.tsum_mul_left,
      tsum_prod' ennreal.summable (λ _, ennreal.summable)],
    exact tsum_congr (λ a, tsum_congr (λ b, trans (by congr) (ite_and_mul_zero _ _ _ _))),
  end
  ... = ⦃e | oa⦄ * ⦃e' | ob⦄ : by simp only [prob_event_eq_tsum]

lemma prob_event_diagonal [hα : decidable_eq α] (oa : oracle_comp spec (α × α)) :
  ⦃set.diagonal α | oa⦄ = ∑' (a : α), ⦃oa⦄ (a, a) :=
calc ⦃set.diagonal α | oa⦄ = ∑' (x : α × α), ite (x ∈ set.diagonal α) (⦃oa⦄ x) 0 :
    prob_event_eq_tsum oa (set.diagonal α)
  ... = ∑' (a a' : α), ite (a = a') (⦃oa⦄ (a, a')) 0 :
    tsum_prod' ennreal.summable (λ _, ennreal.summable)
  ... = ∑' (a a' : α), ite (a = a') (⦃oa⦄ (a, a)) 0 :
    tsum_congr (λ a, tsum_congr (λ a', by by_cases h : a = a'; simp only [h, if_false]))
  ... = ∑' (a a' : α), ite (a' = a) (⦃oa⦄ (a, a)) 0 : by simp_rw [@eq_comm]
  ... = ∑' (a : α), ⦃oa⦄ (a, a) : tsum_congr (λ a, tsum_ite_eq _ _) 

end prob_event

section equiv

end equiv

section indep_events

/-- Any collections of sets corresponding to output types of two computations
  are independent when returning the outputs of the computations in a `prod` type -/
lemma indep_events_prod (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (events₁ : set (set α)) (events₂ : set (set β)) :
  indep_events (oa ×ₘ ob) ((λ e, {x | x.1 ∈ e}) '' events₁) ((λ e, {x | x.2 ∈ e}) '' events₂) :=
sorry

end indep_events

section indep_event

/-- Any events corresponding to two computations respective output types
  are independent when returning the two outputs in a `prod` type -/
lemma indep_event_prod (e₁ : set α) (e₂ : set β)
  (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  indep_event (oa ×ₘ ob) {x | x.1 ∈ e₁} {x | x.2 ∈ e₂} :=
sorry

end indep_event

end distribution_semantics