/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.equiv

/-!
# Distribution Semantics of Bind

This file gives various lemmas for probability outcomes of the computation `oa >>= ob`.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)

section mem_support

variables (x : α) (y : β)

/-- `y` is in the support of `oa >>= ob` iff there is some output of `x` of `oa`
such that `y` is in the support of `ob x`. -/
lemma mem_support_bind_iff : y ∈ (oa >>= ob).support ↔ ∃ x ∈ oa.support, y ∈ (ob x).support :=
by simp_rw [support_bind, set.mem_Union]

lemma mem_fin_support_bind_iff : y ∈ (oa >>= ob).fin_support ↔
  ∃ x ∈ oa.fin_support, y ∈ (ob x).fin_support :=
by rw [fin_support_bind, finset.mem_bUnion]

lemma mem_support_bind (hx : x ∈ oa.support) (hy : y ∈ (ob x).support) : y ∈ (oa >>= ob).support :=
(mem_support_bind_iff oa ob y).2 ⟨x, hx, hy⟩

lemma mem_fin_support_bind (hx : x ∈ oa.fin_support) (hy : y ∈ (ob x).fin_support) :
  y ∈ (oa >>= ob).fin_support :=
(mem_fin_support_bind_iff oa ob y).2 ⟨x, hx, hy⟩

lemma not_mem_support_bind_iff : y ∉ (oa >>= ob).support ↔ ∀ x ∈ oa.support, y ∉ (ob x).support :=
by simp only [support_bind, set.mem_Union, not_exists]

lemma not_mem_fin_support_bind_iff : y ∉ (oa >>= ob).fin_support ↔
  ∀ x ∈ oa.fin_support, y ∉ (ob x).fin_support :=
by simp only [fin_support_bind, finset.mem_bUnion, not_exists]

lemma not_mem_support_bind (h : ∀ x ∈ oa.support, y ∉ (ob x).support) : y ∉ (oa >>= ob).support :=
(not_mem_support_bind_iff oa ob y).2 h

lemma not_mem_fin_support_bind (h : ∀ x ∈ oa.fin_support, y ∉ (ob x).fin_support) :
  y ∉ (oa >>= ob).fin_support :=
(not_mem_fin_support_bind_iff oa ob y).2 h

end mem_support

section eval_dist

/-- The probability of `oa >>= ob` returning `y` is the sum over all `x` of the probability
of getting `y` from `ob x`, weighted by the probability of getting `x` from `oa`. -/
lemma eval_dist_bind_apply_eq_tsum (y : β) :
  ⁅= y | oa >>= ob⁆ = ∑' x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
by rw [eval_dist_bind, pmf.bind_apply]

/-- Express the probability of getting `y` from `oa >>= ob` as a finite sum,
assuming that the underlying return type `α` of `oa` is itself finite. -/
lemma eval_dist_bind_apply_eq_sum (y : β) [fintype α] :
  ⁅= y | oa >>= ob⁆ = ∑ x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
by simpa only [eval_dist_bind_apply_eq_tsum]
  using tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim)

/-- Express the probability of getting `y` from `oa >>= ob` as a sum over `oa.fin_support`. -/
lemma eval_dist_bind_apply_eq_sum_fin_support (y : β) :
  ⁅= y | oa >>= ob⁆ = ∑ x in oa.fin_support, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
(eval_dist_bind_apply_eq_tsum oa ob y).trans
  (tsum_eq_sum (λ x hx, (eval_dist_eq_zero' hx).symm ▸ zero_mul _))

/-- Express the probability of getting `y` from `oa >>= ob` as a finite sum over `s`,
assuming that `s` is a finite subset of `oa.support`. -/
lemma eval_dist_bind_apply_eq_sum_of_support_subset (y : β) (s : finset α) (hs : oa.support ⊆ s) :
  ⁅= y | oa >>= ob⁆ = ∑ x in s, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
(eval_dist_bind_apply_eq_tsum oa ob y).trans (tsum_eq_sum (λ x hx,
  (eval_dist_eq_zero (λ h, hx (finset.mem_coe.1 (hs h)))).symm ▸ (zero_mul _)))

end eval_dist

section prob_event

@[simp] lemma prob_event_bind_eq_tsum (e' : set β) :
  ⁅e' | oa >>= ob⁆ = ∑' x, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
by simp only [prob_event.def, eval_dist_bind, pmf.to_outer_measure_bind_apply]

lemma prob_event_bind_eq_sum [fintype α] (e' : set β) :
  ⁅e' | oa >>= ob⁆ = ∑ x, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
by simpa only [prob_event_bind_eq_tsum] using tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim)

lemma prob_event_bind_eq_sum_fin_support (e' : set β) :
  ⁅e' | oa >>= ob⁆ = ∑ x in oa.fin_support, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
(prob_event_bind_eq_tsum _ _ _).trans (tsum_eq_sum (λ x h, by rw [eval_dist_eq_zero' h, zero_mul]))

theorem prob_event_bind_eq_sum_of_support_subset (e : set β) (s : finset α) (hs : oa.support ⊆ s) :
  ⁅e | oa >>= ob⁆ = ∑ x in s, ⁅oa⁆ x * ⁅e | ob x⁆ :=
(prob_event_bind_eq_tsum oa ob e).trans (tsum_eq_sum (λ x hx,
  (eval_dist_eq_zero (λ h, hx (finset.mem_coe.1 (hs h)))).symm ▸ (zero_mul _)))

end prob_event

section bind_eq_iff

lemma bind_dist_equiv_iff  (ob' : oracle_comp spec' β) :
  (oa >>= ob) ≃ₚ ob' ↔ ∀ y, ∑' (x : α), ⁅= x | oa⁆ * ⁅= y | ob x⁆ = ⁅= y | ob'⁆ :=
by simp only [dist_equiv.ext_iff, eval_dist_bind_apply_eq_tsum]

lemma eval_dist_bind_eq_iff (p : pmf β) :
  ⁅oa >>= ob⁆ = p ↔ ∀ y, ∑' (x : α), ⁅= x | oa⁆ * ⁅= y | ob x⁆ = p y :=
by simp only [eval_dist.ext_iff, eval_dist_bind_apply_eq_tsum]

lemma eval_dist_bind_apply_eq_iff (y : β) (r : ℝ≥0∞) :
  ⁅= y | oa >>= ob⁆ = r ↔ ∑' (x : α), ⁅= x | oa⁆ * ⁅= y | ob x⁆ = r :=
by rw [eval_dist_bind_apply_eq_tsum]

lemma prob_event_bind_eq_iff (e : set β) (r : ℝ≥0∞) :
  ⁅e | oa >>= ob⁆ = r ↔ ∑' (x : α), ⁅= x | oa⁆ * ⁅e | ob x⁆ = r :=
by rw [prob_event_bind_eq_tsum]

end bind_eq_iff

section bind_eq_zero

-- TODO!: Making something like this a simp lemma requires a special "eval_dist" simp class
@[simp] lemma eval_dist_bind_apply_eq_zero_iff (y : β) :
  ⁅= y | oa >>= ob⁆ = 0 ↔ ∀ x ∈ oa.support, y ∉ (ob x).support :=
by simp_rw [pmf.apply_eq_zero_iff, support_eval_dist, support_bind, set.mem_Union, not_exists]

@[simp] lemma prob_event_bind_eq_zero_iff (e : set β) :
  ⁅e | oa >>= ob⁆ = 0 ↔ ∀ x ∈ oa.support, disjoint (ob x).support e :=
by simp only [prob_event_eq_zero_iff_disjoint_support, support_bind, set.disjoint_Union_left]

end bind_eq_zero

section bind_eq_one_iff

@[simp] lemma eval_dist_bind_apply_eq_one_iff (y : β) :
  ⁅= y | oa >>= ob⁆ = 1 ↔ ∀ x ∈ oa.support, (ob x).support ⊆ {y} :=
by simp only [eval_dist_bind, pmf.bind_apply_eq_one_iff, support_eval_dist]

@[simp] lemma prob_event_bind_eq_one_iff (e : set β) :
  ⁅e | oa >>= ob⁆ = 1 ↔ ∀ x ∈ oa.support, (ob x).support ⊆ e :=
by simp only [prob_event_eq_one_iff_support_subset, support_bind, set.Union_subset_iff]

end bind_eq_one_iff

section equiv

/-- If two computations `oa` and `oa'` are distributionally equivalent to each other,
and computations `ob` and `ob'` are equivalent for any input that is an output of `oa`,
then the sequential computations `oa >>= ob` and `oa' >>= ob'` are equivalent. -/
lemma bind_dist_equiv_bind_of_dist_equiv {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  {oa' : oracle_comp spec' α} {ob' : α → oracle_comp spec' β} (ha : oa ≃ₚ oa')
  (hb : ∀ x ∈ oa.support, ob x ≃ₚ ob' x) : (oa >>= ob) ≃ₚ (oa' >>= ob') :=
begin
  refine dist_equiv.ext (λ y, _),
  simp only [eval_dist_bind_apply_eq_tsum],
  refine tsum_congr (λ x, _),
  by_cases hx : x ∈ oa.support,
  { rw [ha.eval_dist_eq, (hb x hx).eval_dist_eq] },
  { simp only [zero_mul, eval_dist_eq_zero hx,
      eval_dist_eq_zero (ha.support_eq ▸ hx : x ∉ oa'.support)] }
end

lemma bind_dist_equiv_bind_of_dist_equiv_left (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oa' : oracle_comp spec α) (h : oa ≃ₚ oa') :
  (oa >>= ob) ≃ₚ (oa' >>= ob) :=
bind_dist_equiv_bind_of_dist_equiv h (λ _ _, rfl)

lemma bind_dist_equiv_bind_of_dist_equiv_right (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (ob' : α → oracle_comp spec β)
  (h' : ∀ x ∈ oa.support, ob x ≃ₚ ob' x) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
bind_dist_equiv_bind_of_dist_equiv rfl h'

end equiv

end oracle_comp