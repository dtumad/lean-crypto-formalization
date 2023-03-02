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

section bind_eq_iff

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)

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

section bind_eq_zero_iff

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)

lemma eval_dist_bind_apply_eq_zero_iff (y : β) :
  ⁅= y | oa >>= ob⁆ = 0 ↔ ∀ x ∈ oa.support, y ∉ (ob x).support :=
by simp_rw [pmf.apply_eq_zero_iff, support_eval_dist, support_bind, set.mem_Union, not_exists]

lemma prob_event_bind_eq_zero_iff (e : set β) :
  ⁅e | oa >>= ob⁆ = 0 ↔ ∀ x ∈ oa.support, disjoint (ob x).support e :=
by simp only [prob_event_eq_zero_iff_disjoint_support, support_bind, set.disjoint_Union_left]

end bind_eq_zero_iff

section bind_eq_one_iff

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)

lemma eval_dist_bind_apply_eq_one_iff (y : β) :
  ⁅= y | oa >>= ob⁆ = 1 ↔ ∀ x ∈ oa.support, (ob x).support ⊆ {y} :=
by simp only [eval_dist_bind, pmf.bind_apply_eq_one_iff, support_eval_dist]

lemma prob_event_bind_eq_one_iff (e : set β) :
  ⁅e | oa >>= ob⁆ = 1 ↔ ∀ x ∈ oa.support, (ob x).support ⊆ e :=
by simp only [prob_event_eq_one_iff_support_subset, support_bind, set.Union_subset_iff]

end bind_eq_one_iff

/-- If two computations `oa` and `oa'` are distributionally equivalent to each other,
and computations `ob` and `ob'` are equivalent for any input that is an output of `oa`,
then the sequential computations `oa >>= ob` and `oa' >>= ob'` are equivalent. -/
lemma bind_dist_equiv_bind_of_dist_equiv (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (oa' : oracle_comp spec' α) (ob' : α → oracle_comp spec' β) (ha : oa ≃ₚ oa')
  (hb : ∀ x ∈ oa.support, ob x ≃ₚ ob' x) : (oa >>= ob) ≃ₚ (oa' >>= ob') :=
begin
  refine dist_equiv.ext (λ y, _),
  simp only [eval_dist_bind_apply_eq_tsum],
  refine tsum_congr (λ x, _),
  by_cases hx : x ∈ oa.support,
  { rw [ha.eval_dist_eq, (hb x hx).eval_dist_eq] },
  { simp only [zero_mul, eval_dist_eq_zero_of_not_mem_support hx,
      eval_dist_eq_zero_of_not_mem_support (ha.support_eq ▸ hx : x ∉ oa'.support)] }
end

lemma bind_dist_equiv_bind_of_dist_equiv_left (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oa' : oracle_comp spec α) (h : oa ≃ₚ oa') :
  (oa >>= ob) ≃ₚ (oa' >>= ob) :=
sorry

lemma bind_dist_equiv_bind_of_dist_equiv_right (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (ob' : α → oracle_comp spec β)
  (h' : ∀ x ∈ oa.support, ob x ≃ₚ ob' x) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
sorry

end oracle_comp