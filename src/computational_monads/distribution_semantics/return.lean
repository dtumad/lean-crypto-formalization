/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.dist_equiv
import computational_monads.distribution_semantics.tactics.tactic_tags

/-!
# Distribution Semantics of Return

This file gives various lemmas for probabilities outcomes of the computation `return a`.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} (spec spec' : oracle_spec) (a a' x : α)

section support

lemma mem_support_return_iff : x ∈ (return' !spec! a).support ↔ x = a := iff.rfl

lemma mem_fin_support_return_iff [decidable_eq α] : x ∈ (return' !spec! a).fin_support ↔ x = a :=
finset.mem_singleton

lemma mem_support_return_self : x ∈ (return' !spec! x).support := set.mem_singleton x

lemma mem_fin_support_return_self [decidable_eq α] : x ∈ (return' !spec! x).fin_support :=
finset.mem_singleton_self x

lemma not_mem_support_return_iff : x ∉ (return' !spec! a).support ↔ x ≠ a :=
by rw [support_return, set.mem_singleton_iff]

lemma not_mem_fin_support_return_iff [decidable_eq α] :
  x ∉ (return' !spec! a).fin_support ↔ x ≠ a :=
by simp only [fin_support_return, finset.mem_singleton]

lemma not_mem_support_return_of_ne {a x : α} (h : x ≠ a) : x ∉ (return' !spec! a).support :=
by simp only [h, support_return, set.mem_singleton_iff, not_false_iff]

lemma not_mem_fin_support_return_of_ne [decidable_eq α] {a x : α} (h : x ≠ a) :
  x ∉ (return' !spec! a).fin_support :=
by simp only [h, fin_support_return, finset.mem_singleton, not_false_iff]

end support

section prob_output

/-- The probability of getting `x` from `return a` is `1` if `x = a` and `0` if `x ≠ a`.
Without a `decidable_eq` instance the output probabilities use `set.indicator`. -/
lemma prob_output_return_eq_indicator :
  ⁅= x | return' !spec! a⁆ = set.indicator {a} (λ _, 1) x := rfl

/-- The probability of getting `x` from `return a` is `1` if `x = a` and `0` if `x ≠ a`. -/
@[simp] lemma prob_output_return [decidable_eq α] :
  ⁅= x | return' !spec! a⁆ = ite (x = a) 1 0 := by convert rfl

/-- `x` has probability of `0` of being the output of `return a` iff `x ≠ a`. -/
lemma prob_output_return_eq_zero_iff : ⁅= x | return' !spec! a⁆ = 0 ↔ x ≠ a :=
by simp only [prob_output_eq_zero_iff, support_return, set.mem_singleton_iff]

/-- The probability of getting a value besides `a` from `return a` is `0`. -/
lemma prob_output_return_of_ne {a x : α} (h : x ≠ a) : ⁅= x | return' !spec! a⁆ = 0 :=
by rwa [prob_output_return_eq_zero_iff]

/-- `x` has a probability of `1` of being the output of `return a` iff `x = a`. -/
@[simp] lemma prob_output_return_eq_one_iff : ⁅= x | return' !spec! a⁆ = 1 ↔ x = a :=
by rw [prob_output_eq_one_iff_subset, support_return, set.singleton_subset_singleton, eq_comm]

lemma prob_output_return_of_eq {a x : α} (h : x = a) : ⁅= x | return' !spec! a⁆ = 1 :=
by rwa [prob_output_return_eq_one_iff]

@[simp] lemma prob_output_return_self {a : α} : ⁅= a | return' !spec! a⁆ = 1 :=
prob_output_return_of_eq spec rfl

@[simp] lemma tsum_prob_output_return (spec : oracle_spec) (x : α) :
  ∑' y : α, ⁅= x | (return y : oracle_comp spec α)⁆ = 1 :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  simp [@eq_comm _ x],
end

end prob_output

section prob_event

lemma prob_event_return_eq_indicator (p : α → Prop) :
  ⁅p | return' !spec! a⁆ = set.indicator p (λ _, 1) a :=
by rw [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply, set.indicator]

@[simp] lemma prob_event_return (p : α → Prop) [decidable_pred p] :
  ⁅p | return' !spec! a⁆ = if p a then 1 else 0 :=
by { simp only [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply], congr }

lemma prob_event_return_eq_zero_iff (p : α → Prop) : ⁅p | return' !spec! a⁆ = 0 ↔ ¬ p a :=
by simp only [prob_event_return_eq_indicator, set.indicator_apply_eq_zero,
  set.mem_def, one_ne_zero, imp_false]

lemma prob_event_return_of_neg {a : α} {p : α → Prop} (h : ¬ p a) : ⁅p | return' !spec! a⁆ = 0 :=
by rwa [prob_event_return_eq_zero_iff]

lemma prob_event_return_eq_one_iff (p : α → Prop) : ⁅p | return' !spec! a⁆ = 1 ↔ p a :=
by rw [prob_event.def, eval_dist_return, pmf.to_outer_measure_apply_eq_one_iff,
  pmf.support_pure, set.singleton_subset_iff, set.mem_def]

lemma prob_event_return_of_pos {a : α} {p : α → Prop} (h : p a) : ⁅p | return' !spec! a⁆ = 1 :=
by rwa [prob_event_return_eq_one_iff]

@[simp] lemma tsum_prob_event_mem_finset_return (spec : oracle_spec) (s : finset α) :
  ∑' x : α, ⁅(∈ s) | (return x : oracle_comp spec α)⁆ = s.card :=
calc ∑' x : α, ⁅(∈ s) | (return x : oracle_comp spec α)⁆ =
  ∑ x in s, ⁅(∈ s) | (return x : oracle_comp spec α)⁆ :
    tsum_eq_sum (λ x hx, prob_event_return_of_neg spec hx)
  ... = ∑ x in s, 1 : finset.sum_congr rfl (λ x hx, prob_event_return_of_pos spec hx)
  ... = s.card : by rw [finset.sum_const, nsmul_one]

end prob_event

/-- Any set of events are independent with respect to the computation `return a`. -/
@[simp] lemma indep_events_return (es es' : set (α → Prop)) :
  (return' !spec! a).indep_events es es' :=
begin
  refine (indep_events_iff _ _ _).2 (λ p q hp hq, _),
  haveI : decidable_pred p := classical.dec_pred p,
  haveI : decidable_pred q := classical.dec_pred q,
  simp_rw [prob_event_return, ite_and, ite_mul, one_mul, zero_mul]
end

/-- Any pair of events are independent with respect to the computation `return a`. -/
@[simp] lemma indep_event_return (p q : α → Prop) : (return' !spec! a).indep_event p q :=
indep_events_return spec a {p} {q}

section return_eq_iff

/-- `return a` has the same distribution as `oa` iff outputs besides `a` have `0` probability. -/
lemma return_dist_equiv_iff {spec' : oracle_spec} (oa : oracle_comp spec' α) :
  (return' !spec! a) ≃ₚ oa ↔ ∀ x ≠ a, ⁅= x | oa⁆ = 0 :=
by simp_rw [dist_equiv, eval_dist_return, pmf.pure_eq_iff, prob_output]

/-- `return a` has the same distribution as `oa` iff outputs besides `a` have `0` probability. -/
lemma dist_equiv_return_iff {spec' : oracle_spec} (oa : oracle_comp spec' α) :
  oa ≃ₚ (return' !spec! a) ↔ ∀ x ≠ a, ⁅= x | oa⁆ = 0 :=
by rw [dist_equiv.symm_iff, return_dist_equiv_iff]

lemma return_dist_equiv_iff' (oa : oracle_comp spec α) (x : α) :
  (return' !spec! x) ≃ₚ oa ↔ oa.support = {x} :=
begin
  rw [dist_equiv.symm_iff],
  refine ⟨λ h, h.support_eq.trans (support_return _ _), λ h, dist_equiv.ext (λ y, _)⟩,
  by_cases hy : y = x,
  { rwa [hy, prob_output_return_self, prob_output_eq_one_iff] },
  { rwa [prob_output_return_of_ne _ hy, prob_output_eq_zero_iff, h, set.mem_singleton_iff] }
end

lemma dist_equiv_return_iff' (oa : oracle_comp spec α) (x : α) :
  oa ≃ₚ (return' !spec! x) ↔ oa.support = {x} :=
by rw [dist_equiv.symm_iff, return_dist_equiv_iff']

lemma support_return_eq_iff (s : set α) :
  (return' !spec! a).support = s ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
by rw [support_return, @eq_comm _ {a} s, set.eq_singleton_iff_unique_mem]

lemma fin_support_return_eq_iff [decidable_eq α] (s : finset α) :
  (return' !spec! a).fin_support = s ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
by simp_rw [fin_support_eq_iff_support_eq_coe, support_return_eq_iff, finset.mem_coe]

lemma eval_dist_return_eq_iff (p : pmf α) :
  ⁅return' !spec! a⁆ = p ↔ ∀ x ≠ a, p x = 0 :=
by rw [eval_dist_return, pmf.pure_eq_iff]

lemma prob_output_return_eq_iff (x : α) (r : ℝ≥0∞) :
  ⁅= x | return' !spec! a⁆ = r ↔ (x = a ∧ r = 1) ∨ (x ≠ a ∧ r = 0) :=
by simp_rw [prob_output_return_eq_indicator, set.indicator, ite_eq_iff,
  set.mem_singleton_iff, @eq_comm ℝ≥0∞ 1, @eq_comm ℝ≥0∞ 0]

lemma prob_event_return_eq_iff (p : α → Prop) (r : ℝ≥0∞) :
  ⁅p | return' !spec! a⁆ = r ↔ (p a ∧ r = 1) ∨ (¬ p a ∧ r = 0) :=
by rw [prob_event_return_eq_indicator, set.indicator, ite_eq_iff, @eq_comm ℝ≥0∞ 1,
  @eq_comm ℝ≥0∞ 0, set.mem_def]

/-- Two `return` computations are distributionally equivalent iff they return the same value. -/
@[simp] lemma return_dist_equiv_return_iff' :
  (return' !spec! a) ≃ₚ (return' !spec'! a') ↔ a = a' :=
begin
  simp only [return_dist_equiv_iff, prob_output_return_eq_zero_iff],
  exact ⟨λ h, by simpa only [ne.def, imp_not_comm, eq_self_iff_true, not_not,
    true_implies_iff, @eq_comm _ a' a] using h a', λ h x hx, h ▸ hx⟩,
end

@[pairwise_dist_equiv] lemma return_dist_equiv_return :
  (return' !spec! a) ≃ₚ (return' !spec'! a) := (return_dist_equiv_return_iff' spec spec' a a).2 rfl

lemma return_dist_equiv_return_of_eq (h : a = a') : (return' !spec! a) ≃ₚ (return' !spec'! a') :=
by rwa [return_dist_equiv_return_iff']

end return_eq_iff

end oracle_comp