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

variables {α β γ : Type} (spec spec' : oracle_spec) (a a' : α)

section mem_support

variable (x : α)

lemma mem_support_return_iff : x ∈ (return' !spec! a).support ↔ x = a := iff.rfl

lemma mem_fin_support_return_iff [decidable_eq α] : x ∈ (return' !spec! a).fin_support ↔ x = a :=
finset.mem_singleton

lemma mem_support_return_self : x ∈ (return' !spec! x).support := set.mem_singleton x

lemma mem_fin_support_return_self [decidable_eq α] : x ∈ (return' !spec! x).fin_support :=
finset.mem_singleton_self x

lemma not_mem_support_return_iff :
  x ∉ (return' !spec! a).support ↔ x ≠ a :=
by rw [support_return, set.mem_singleton_iff]

lemma not_mem_fin_support_return_iff [decidable_eq α] :
  x ∉ (return' !spec! a).fin_support ↔ x ≠ a :=
by simp only [fin_support_return, finset.mem_singleton]

lemma not_mem_support_of_ne {a x : α} (h : x ≠ a) :
  x ∉ (return' !spec! a).support :=
by simp only [h, support_return, set.mem_singleton_iff, not_false_iff]

lemma not_mem_fin_support_of_ne [decidable_eq α] {a x : α} (h : x ≠ a) :
  x ∉ (return' !spec! a).fin_support :=
by simp only [h, fin_support_return, finset.mem_singleton, not_false_iff]

end mem_support

section eval_dist

/-- The probability of getting `x` from `return a` is `1` if `x = a` and `0` if `x ≠ a`.
Without a `decidable_eq` instance the output probabilities use `set.indicator`. -/
lemma prob_output_return_eq_indicator (x : α) :
  ⁅= x | return' !spec! a⁆ = set.indicator {a} (λ _, 1) x := rfl

/-- The probability of getting `x` from `return a` is `1` if `x = a` and `0` if `x ≠ a`. -/
lemma prob_output_return [decidable_eq α] (x : α) :
  ⁅= x | return' !spec! a⁆ = ite (x = a) 1 0 := by convert rfl

end eval_dist

section prob_event

@[simp] lemma prob_event_return_eq_indicator (e : set α) :
  ⁅e | return' !spec! a⁆ = e.indicator (λ _, 1) a :=
by rw [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply, set.indicator]

@[simp] lemma prob_event_return (e : set α) [decidable_pred (∈ e)] :
  ⁅e | return' !spec! a⁆ = ite (a ∈ e) 1 0 :=
by { simp only [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply], congr }

@[simp] lemma prob_event_return' (p : α → Prop) [decidable_pred p] :
  ⁅p | return' !spec! a⁆ = ite (p a) 1 0 := by simpa

end prob_event

section return_eq_zero

/-- `x` has probability of `0` of being the output of `return a` iff `x ≠ a`. -/
lemma prob_output_return_eq_zero_iff (x : α) : ⁅= x | return' !spec! a⁆ = 0 ↔ x ≠ a :=
by simp only [prob_output_eq_zero_iff, support_return, set.mem_singleton_iff]

lemma prob_event_return_eq_zero_iff (e : set α) : ⁅e | return' !spec! a⁆ = 0 ↔ a ∉ e :=
by simp only [prob_event_return_eq_indicator, set.indicator_apply_eq_zero, one_ne_zero, imp_false]

/-- The probability of getting a value besides `a` from `return a` is `0`. -/
lemma prob_output_return_of_ne {a x : α} (h : x ≠ a) : ⁅= x | return' !spec! a⁆ = 0 :=
by simpa only [prob_output_eq_zero_iff]

lemma prob_event_return_of_not_mem {a} {e : set α} (h : a ∉ e) :
  ⁅e | return' !spec! a⁆ = 0 :=
by rwa [prob_event_eq_zero_iff_disjoint_support, support_return, set.disjoint_singleton_left]

lemma prob_event_diff_of_mem {a} (e : set α) {e' : set α} (h : a ∈ e') :
  ⁅e \ e' | return' !spec! a⁆ = 0 :=
prob_event_return_of_not_mem spec (set.not_mem_diff_of_mem h)

lemma prob_event_return_diff_self (e : set α) : ⁅e \ {a} | return' !spec! a⁆ = 0 :=
prob_event_diff_of_mem spec e (set.mem_singleton a)

lemma prob_event_return_inter_of_not_mem_left (e e' : set α) (h : a ∉ e) :
  ⁅e ∩ e' | return' !spec! a⁆ = 0 :=
prob_event_return_of_not_mem spec (λ h', h h'.1)

lemma prob_event_return_inter_of_not_mem_right (e e' : set α) (h : a ∉ e') :
  ⁅e ∩ e' | return' !spec! a⁆ = 0 :=
prob_event_return_of_not_mem spec (λ h', h h'.2)

end return_eq_zero

section return_eq_one

/-- `x` has a probability of `1` of being the output of `return a` iff `x = a`. -/
lemma prob_output_return_eq_one_iff (x : α) : ⁅= x | return' !spec! a⁆ = 1 ↔ x = a :=
by rw [prob_output_eq_one_iff, support_return, @eq_comm _ x, set.singleton_eq_singleton_iff]

lemma prob_event_return_eq_one_iff (e : set α) : ⁅e | return' !spec! a⁆ = 1 ↔ a ∈ e :=
by rw [prob_event.def, eval_dist_return, pmf.to_outer_measure_apply_eq_one_iff,
  pmf.support_pure, set.singleton_subset_iff]

lemma prob_output_return_of_eq {a x : α} (h : x = a) : ⁅= x | return' !spec! a⁆ = 1 :=
(prob_output_return_eq_one_iff _ a x).2 h

lemma prob_event_return_of_mem {e : set α} (h : a ∈ e) : ⁅e | return' !spec! a⁆ = 1 :=
(prob_event_return_eq_one_iff _ a e).2 h

@[simp] lemma prob_output_return_self : ⁅= a | return' !spec! a⁆ = 1 :=
by rw [prob_output_return_eq_one_iff]

lemma prob_event_return_singleton_self : ⁅{a} | return' !spec! a⁆ = 1 :=
by rw [prob_event_singleton_eq_prob_output, prob_output_return_self]

lemma prob_event_return_insert_self (s : set α) : ⁅insert a s | return' !spec! a⁆ = 1 :=
by rw [prob_event_insert, prob_output_return_self, prob_event_return_diff_self, add_zero]

end return_eq_one

section return_pos

-- TODO

end return_pos

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

lemma prob_event_return_eq_iff (e : set α) (r : ℝ≥0∞) :
  ⁅e | return' !spec! a⁆ = r ↔ (a ∈ e ∧ r = 1) ∨ (a ∉ e ∧ r = 0) :=
by rw [prob_event_return_eq_indicator, set.indicator, ite_eq_iff, @eq_comm ℝ≥0∞ 1, @eq_comm ℝ≥0∞ 0]

end return_eq_iff

section return_eq_return_iff

/-- Two `return` computations are distributionally equivalent iff they return the same value. -/
@[simp] lemma return_dist_equiv_return_iff' : (return' !spec! a) ≃ₚ (return' !spec'! a') ↔ a = a' :=
begin
  simp only [return_dist_equiv_iff, prob_output_return_eq_zero_iff],
  exact ⟨λ h, by simpa only [ne.def, imp_not_comm, eq_self_iff_true, not_not,
    true_implies_iff, @eq_comm _ a' a] using h a', λ h x hx, h ▸ hx⟩,
end

@[pairwise_dist_equiv]
lemma return_dist_equiv_return : (return' !spec! a) ≃ₚ (return' !spec'! a) :=
(return_dist_equiv_return_iff' spec spec' a a).2 rfl

lemma support_return_eq_support_return_iff :
  (return' !spec! a).support = (return' !spec'! a').support ↔ a = a' :=
by simp only [support_return, set.singleton_eq_singleton_iff]

lemma fin_support_return_eq_fin_support_return_iff [decidable_eq α] :
  (return' !spec! a).fin_support = (return' !spec'! a').fin_support ↔ a = a' :=
by simp only [fin_support_return, finset.singleton_inj]

lemma eval_dist_return_eq_eval_dist_return_iff :
  ⁅return' !spec! a⁆ = ⁅return' !spec'! a'⁆ ↔ a = a' :=
return_dist_equiv_return_iff' spec spec' a a'

lemma prob_output_return_eq_prob_output_return_iff (x y : α) :
  ⁅= x | return' !spec! a⁆ = ⁅= y | return' !spec'! a'⁆ ↔ (x = a ↔ y = a') :=
by simpa only [prob_output_return_eq_iff, eq_self_iff_true, one_ne_zero, zero_ne_one,
  and_true, and_false, or_false, false_or] using (iff_iff_and_or_not_and_not).symm

lemma prob_event_return_eq_prob_event_return_iff (e e' : set α) :
  ⁅e | return' !spec! a⁆ = ⁅e' | return' !spec'! a'⁆ ↔ (a ∈ e ↔ a' ∈ e') :=
by simpa only [prob_event_return_eq_iff, eq_self_iff_true, one_ne_zero, zero_ne_one,
  and_true, and_false, or_false, false_or] using (iff_iff_and_or_not_and_not).symm

lemma return_dist_equiv_return_of_eq (h : a = a') :
  (return' !spec! a) ≃ₚ (return' !spec'! a') :=
by rwa [return_dist_equiv_return_iff']

end return_eq_return_iff

section indep_events

/-- Any set of events are independent with respect to the computation `return a`. -/
@[simp] lemma indep_events_return (es es' : set (set α)) :
  (return' !spec! a).indep_events es es' :=
begin
  refine (indep_events_iff _ _ _).2 (λ e e' he he', _),
  simp only [indep_event_iff, prob_event_return_eq_indicator, set.indicator],
  by_cases ha : a ∈ e ∩ e',
  { simp only [ha, ha.1, ha.2, if_true, mul_one] },
  { refine trans (by simp only [ha, if_false]) (mul_eq_zero.2 _).symm,
    simpa only [ite_eq_right_iff, one_ne_zero, imp_false, ← not_and_distrib] using ha },
end

/-- Any pair of events are independent with respect to the computation `return a`. -/
@[simp] lemma indep_event_return (e e' : set α) :
  (return' !spec! a).indep_event e e' :=
indep_event_of_indep_events _ e e' (indep_events_return spec a {e} {e'})

end indep_events

end oracle_comp