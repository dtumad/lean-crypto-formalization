/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.dist_equiv
import computational_monads.distribution_semantics.tactics.tactic_tags

/-!
# Distribution Semantics of Bind

This file gives various lemmas for probability outcomes of the computation `oa >>= ob`.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

section support

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (x : α) (y : β)

/-- `y` is in the support of `oa >>= ob` iff there is some output of `x` of `oa`
such that `y` is in the support of `ob x`. -/
lemma mem_support_bind_iff : y ∈ (oa >>= ob).support ↔
  ∃ x ∈ oa.support, y ∈ (ob x).support := by simp_rw [support_bind, set.mem_Union]

lemma mem_support_bind (hx : x ∈ oa.support) (hy : y ∈ (ob x).support) :
  y ∈ (oa >>= ob).support := (mem_support_bind_iff oa ob y).2 ⟨x, hx, hy⟩

lemma not_mem_support_bind_iff : y ∉ (oa >>= ob).support ↔
  ∀ x ∈ oa.support, y ∉ (ob x).support := by simp only [support_bind, set.mem_Union, not_exists]

lemma not_mem_support_bind (h : ∀ x ∈ oa.support, y ∉ (ob x).support) : y ∉ (oa >>= ob).support :=
(not_mem_support_bind_iff oa ob y).2 h

end support

section fin_support

variables [decidable_eq α] [decidable_eq β] (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β)(x : α) (y : β)

lemma mem_fin_support_bind_iff : y ∈ (oa >>= ob).fin_support ↔
  ∃ x ∈ oa.fin_support, y ∈ (ob x).fin_support :=
by rw [fin_support_bind, finset.mem_bUnion]

lemma mem_fin_support_bind (hx : x ∈ oa.fin_support) (hy : y ∈ (ob x).fin_support) :
  y ∈ (oa >>= ob).fin_support :=
(mem_fin_support_bind_iff oa ob y).2 ⟨x, hx, hy⟩

lemma not_mem_fin_support_bind_iff : y ∉ (oa >>= ob).fin_support ↔
  ∀ x ∈ oa.fin_support, y ∉ (ob x).fin_support :=
by simp only [fin_support_bind, finset.mem_bUnion, not_exists]

lemma not_mem_fin_support_bind (h : ∀ x ∈ oa.fin_support, y ∉ (ob x).fin_support) :
  y ∉ (oa >>= ob).fin_support :=
(not_mem_fin_support_bind_iff oa ob y).2 h

end fin_support

section prob_output

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (y : β)

/-- The probability of `oa >>= ob` returning `y` is the sum over all `x` of the probability
of getting `y` from `ob x`, weighted by the probability of getting `x` from `oa`. -/
lemma prob_output_bind_eq_tsum : ⁅= y | oa >>= ob⁆ = ∑' x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
by simp only [prob_output, eval_dist_bind, pmf.bind_apply]

lemma prob_output_bind_eq_tsum_indicator :
  ⁅= y | oa >>= ob⁆ = ∑' x, oa.support.indicator (λ x, ⁅= x | oa⁆ * ⁅= y | ob x⁆) x :=
(prob_output_bind_eq_tsum oa ob y).trans (tsum_congr (λ x, symm (set.indicator_apply_eq_self.2
  (λ hx, mul_eq_zero_of_left (prob_output_eq_zero hx) _))))

lemma prob_output_bind_eq_tsum_subtype :
  ⁅= y | oa >>= ob⁆ = ∑' x : oa.support, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
trans (prob_output_bind_eq_tsum_indicator oa ob y) (tsum_subtype oa.support _).symm

/-- Express the probability of getting `y` from `oa >>= ob` as a finite sum over `s`,
assuming that `s` is a finite subset of `oa.support`. -/
lemma prob_output_bind_eq_sum_of_subset (s : finset α) (hs : oa.support ⊆ s) :
  ⁅= y | oa >>= ob⁆ = ∑ x in s, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
(prob_output_bind_eq_tsum oa ob y).trans (tsum_eq_sum (λ x hx,
  (prob_output_eq_zero (λ h, hx (finset.mem_coe.1 (hs h)))).symm ▸ (zero_mul _)))

/-- Express the probability of getting `y` from `oa >>= ob` as a sum over `oa.fin_support`.
TODO: make this the default as `prob_output_bind_eq_sum`, that version can use a tick mark. -/
lemma prob_output_bind_eq_sum [decidable_eq α] :
  ⁅= y | oa >>= ob⁆ = ∑ x in oa.fin_support, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
prob_output_bind_eq_sum_of_subset oa ob y oa.fin_support (support_subset_coe_fin_support oa)

/-- Express the probability of getting `y` from `oa >>= ob` as a finite sum,
assuming that the underlying return type `α` of `oa` is itself finite. -/
lemma prob_output_bind_eq_sum_fintype [fintype α] :
  ⁅= y | oa >>= ob⁆ = ∑ x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
prob_output_bind_eq_sum_of_subset oa ob y finset.univ (by simp)

lemma prob_output_bind_eq_zero_iff (y : β) :
  ⁅= y | oa >>= ob⁆ = 0 ↔ ∀ x ∈ oa.support, y ∉ (ob x).support :=
by simp only [prob_output_eq_zero_iff, support_bind, set.mem_Union, not_exists]

lemma prob_output_bind_eq_one_iff (y : β) :
  ⁅= y | oa >>= ob⁆ = 1 ↔ ∀ x ∈ oa.support, (ob x).support ⊆ {y} :=
by simp [prob_output_eq_one_iff_subset]

end prob_output

section prob_event

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (p : β → Prop)

lemma prob_event_bind_eq_tsum : ⁅p | oa >>= ob⁆ = ∑' x, ⁅= x | oa⁆ * ⁅p | ob x⁆ :=
by simp only [prob_output.def, prob_event.def, eval_dist_bind, pmf.to_outer_measure_bind_apply]

lemma prob_event_bind_eq_tsum_indicator :
  ⁅p | oa >>= ob⁆ = ∑' x, oa.support.indicator (λ x, ⁅= x | oa⁆ * ⁅p | ob x⁆) x :=
(prob_event_bind_eq_tsum oa ob p).trans (tsum_congr (λ x, symm (set.indicator_apply_eq_self.2
  (λ hx, mul_eq_zero_of_left (prob_output_eq_zero hx) _))))

lemma prob_event_bind_eq_tsum_subtype :
  ⁅p | oa >>= ob⁆ = ∑' x : oa.support, ⁅= x | oa⁆ * ⁅p | ob x⁆ :=
trans (prob_event_bind_eq_tsum_indicator oa ob p) (tsum_subtype oa.support _).symm

lemma prob_event_bind_eq_sum_of_support_subset (s : finset α) (hs : oa.support ⊆ s) :
  ⁅p | oa >>= ob⁆ = ∑ x in s, ⁅= x | oa⁆ * ⁅p | ob x⁆ :=
(prob_event_bind_eq_tsum oa ob p).trans (tsum_eq_sum (λ x hx, let hx' : x ∉ oa.support :=
  λ h, hx (finset.mem_coe.1 (hs h)) in by simp [mul_eq_zero, prob_output_eq_zero_iff, hx']))

lemma prob_event_bind_eq_sum [decidable_eq α] :
  ⁅p | oa >>= ob⁆ = ∑ x in oa.fin_support, ⁅= x | oa⁆ * ⁅p | ob x⁆ :=
prob_event_bind_eq_sum_of_support_subset oa ob p oa.fin_support (support_subset_coe_fin_support oa)

lemma prob_event_bind_eq_sum_fintype [fintype α] :
  ⁅p | oa >>= ob⁆ = ∑ x, ⁅= x | oa⁆ * ⁅p | ob x⁆ :=
prob_event_bind_eq_sum_of_support_subset oa ob p finset.univ (by simp)

@[simp] lemma prob_event_bind_eq_zero_iff :
  ⁅p | oa >>= ob⁆ = 0 ↔ ∀ x ∈ oa.support, ∀ y ∈ (ob x).support, ¬ p y :=
by simpa only [prob_event_eq_zero_iff, imp_forall_iff, support_bind, set.mem_Union,
  forall_exists_index] using forall_swap

@[simp] lemma prob_event_bind_eq_one_iff :
  ⁅p | oa >>= ob⁆ = 1 ↔ ∀ x ∈ oa.support, ∀ y ∈ (ob x).support, p y :=
by simpa only [prob_event_eq_one_iff, imp_forall_iff, support_bind, set.mem_Union,
  forall_exists_index] using forall_swap

end prob_event

section dist_equiv

/-- If two computations `oa` and `oa'` are distributionally equivalent to each other,
and computations `ob` and `ob'` are equivalent for any input that is an output of `oa`,
then the sequential computations `oa >>= ob` and `oa' >>= ob'` are equivalent. -/
lemma bind_dist_equiv_bind_of_dist_equiv {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  {oa' : oracle_comp spec' α} {ob' : α → oracle_comp spec' β} (ha : oa ≃ₚ oa')
  (hb : ∀ x ∈ oa.support, ob x ≃ₚ ob' x) : (oa >>= ob) ≃ₚ (oa' >>= ob') :=
begin
  refine dist_equiv.ext (λ y, _),
  simp only [prob_output_bind_eq_tsum],
  refine tsum_congr (λ x, _),
  by_cases hx : x ∈ oa.support,
  { rw [ha.prob_output_eq, (hb x hx).prob_output_eq] },
  { simp only [zero_mul, prob_output_eq_zero hx,
      prob_output_eq_zero (ha.support_eq ▸ hx : x ∉ oa'.support)] }
end

lemma bind_dist_equiv_bind_of_dist_equiv_left {oa oa' : oracle_comp spec α}
  (ob : α → oracle_comp spec β) (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
bind_dist_equiv_bind_of_dist_equiv h (λ _ _, rfl)

-- TODO: implicit arguments??
lemma bind_dist_equiv_bind_of_dist_equiv_right
  (oa : oracle_comp spec α) {ob ob' : α → oracle_comp spec β}
  (h' : ∀ x ∈ oa.support, ob x ≃ₚ ob' x) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
bind_dist_equiv_bind_of_dist_equiv rfl h'

lemma bind_dist_equiv_bind_of_dist_equiv_right'
  (oa : oracle_comp spec α) {ob ob' : α → oracle_comp spec β}
  (h' : ∀ x, ob x ≃ₚ ob' x) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
bind_dist_equiv_bind_of_dist_equiv rfl (λ x _, h' x)

lemma bind_dist_equiv_right (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (x : α) (h : ∀ x' ∈ oa.support, ob x' ≃ₚ ob x) : oa >>= ob ≃ₚ ob x :=
begin
  refine (dist_equiv.ext (λ y, _)),
  calc ⁅= y | oa >>= ob⁆ = ∑' x', ⁅= x' | oa⁆ * ⁅= y | ob x'⁆ : prob_output_bind_eq_tsum _ _ y
    ... = ∑' x', ⁅= x' | oa⁆ * ⁅= y | ob x⁆ : begin
      refine tsum_congr (λ x', _),
      by_cases hx' : x' ∈ oa.support,
      { rw [(h _ hx').prob_output_eq] },
      { simp_rw [prob_output_eq_zero hx', zero_mul] }
    end
    ... = ⁅= y | ob x⁆ : by rw [ennreal.tsum_mul_right, oa.tsum_prob_output, one_mul]
end

lemma bind_dist_equiv_left (oa : oracle_comp spec α) (oa' : α → oracle_comp spec α)
  (h : ∀ x ∈ oa.support, oa' x ≃ₚ (return x : oracle_comp spec α)) : oa >>= oa' ≃ₚ oa :=
(bind_dist_equiv_bind_of_dist_equiv_right _ h).trans (dist_equiv.ext (λ x,
  by simp only [prob_output.def, eval_dist_bind, eval_dist_return, pmf.bind_pure]))

end dist_equiv

section bind_mono

lemma prob_output_bind_mono_left {oa oa' : oracle_comp spec α} {ob : α → oracle_comp spec β}
  {y : β} (h : ∀ x, y ∈ (ob x).support → ⁅= x | oa⁆ ≤ ⁅= x | oa'⁆) :
  ⁅= y | oa >>= ob⁆ ≤ ⁅= y | oa' >>= ob⁆ :=
begin
  simp_rw [prob_output_bind_eq_tsum],
  refine ennreal.tsum_le_tsum (λ x, _),
  by_cases hy : ⁅= y | ob x⁆ = 0,
  { simp only [hy, mul_zero, le_zero_iff] },
  { refine (ennreal.mul_le_mul_right hy (prob_output_ne_top _ _)).2
      (h x $ (prob_output_ne_zero_iff _ _).1 hy) }
end

lemma prob_output_bind_mono_right {oa : oracle_comp spec α} {ob ob' : α → oracle_comp spec β}
  {y : β} (h : ∀ x ∈ oa.support, ⁅= y | ob x⁆ ≤ ⁅= y | ob' x⁆) :
  ⁅= y | oa >>= ob⁆ ≤ ⁅= y | oa >>= ob'⁆ :=
begin
  simp_rw [prob_output_bind_eq_tsum],
  refine ennreal.tsum_le_tsum (λ x, _),
  by_cases hx : ⁅= x | oa⁆ = 0,
  { simp only [hx, zero_mul, le_zero_iff] },
  { exact (ennreal.mul_le_mul_left hx (prob_output_ne_top _ _)).2
      (h x $ (prob_output_ne_zero_iff _ _).1 hx) }
end

end bind_mono

section bind_of_const

lemma prob_output_bind_of_const {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  (y : β) (r : ℝ≥0∞) (hr : ∀ x ∈ oa.support, ⁅= y | ob x⁆ = r) :
  ⁅= y | oa >>= ob⁆ = r :=
begin
  have : ∑' x, ⁅= x | oa⁆ * r = r,
  by simp [ennreal.tsum_mul_right],
  refine trans (trans (prob_output_bind_eq_tsum _ _ _) (tsum_congr (λ x, _))) this,
  by_cases hx : ⁅= x | oa⁆ = 0,
  { simp only [hx, zero_mul] },
  { rw [hr x ((prob_output_ne_zero_iff _ _).1 hx)] }
end

end bind_of_const

end oracle_comp