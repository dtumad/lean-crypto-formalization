/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.basic

/-!
# Distributional Semantics of Simulation of a Return Operation

This file contains lemmas about the computation `simulate so (return x) s`.
-/

variables {α β γ : Type} {spec spec' : oracle_spec} {S : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables (so : sim_oracle spec spec' S) (a : α) (s : S)

section support

@[simp] lemma support_simulate_return : (simulate so (return a) s).support = {(a, s)} := rfl

lemma mem_support_simulate_return_iff (x : α × S) :
  x ∈ (simulate so (return a) s).support ↔ x.1 = a ∧ x.2 = s :=
by simp [prod.eq_iff_fst_eq_snd_eq]

lemma support_simulate'_return : (simulate' so (return a) s).support = {a} := by simp

lemma mem_support_simulate'_return_iff (x : α) :
  x ∈ (simulate' so (return a) s).support ↔ x = a := by simp

end support

section fin_support

@[simp] lemma fin_support_simulate_return :
  (simulate so (return a) s).fin_support = {(a, s)} := rfl

lemma mem_fin_support_simulate_return_iff (x : α × S) :
  x ∈ (simulate so (return a) s).fin_support ↔ x.1 = a ∧ x.2 = s :=
by simp [prod.eq_iff_fst_eq_snd_eq]

@[simp] lemma fin_support_simulate'_return : (simulate' so (return a) s).fin_support = {a} :=
by simp [simulate'_return]

lemma mem_fin_support_simulate'_return_iff (x : α) :
  x ∈ (simulate' so (return a) s).support ↔ x = a := by simp

end fin_support

section eval_dist

@[simp] lemma eval_dist_simulate_return : ⁅simulate so (return a) s⁆ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate'_return : ⁅simulate' so (return a) s⁆ = pmf.pure a := by simp

end eval_dist

section dist_equiv

-- @[simp_dist_equiv] lemma simulate_return_dist_equiv' :
--   simulate so (return a) s ≃ₚ (return' !spec! (a, s)) := refl _

@[simp, simp_dist_equiv] lemma simulate_return_dist_equiv :
  simulate so (return a) s ≃ₚ (return' !spec'! (a, s)) := refl _

-- @[simp_dist_equiv] lemma simulate'_return_dist_equiv' :
--   simulate' so (return a) s ≃ₚ (return' !spec! a) := by pairwise_dist_equiv

@[simp, simp_dist_equiv] lemma simulate'_return_dist_equiv :
  simulate' so (return a) s ≃ₚ (return' !spec'! a) := by simp [simulate'_return]

end dist_equiv

section prob_output

@[simp] lemma prob_output_simulate_return_eq_indicator (x : α × S) :
  ⁅= x | simulate so (return a) s⁆ = set.indicator {(a, s)} (λ _, 1) x :=
prob_output_return_eq_indicator _ _ _

@[simp] lemma prob_output_simulate_return [decidable_eq α] [decidable_eq S] (x : α × S) :
  ⁅= x | simulate so (return a) s⁆ = if x = (a, s) then 1 else 0 :=
prob_output_return _ _ _

@[simp] lemma prob_output_simulate'_return_eq_indicator (x : α) :
  ⁅= x | simulate' so (return a) s⁆ = set.indicator {a} (λ _, 1) x :=
by simp [simulate'_return, prob_output_return_eq_indicator]

@[simp] lemma prob_output_simulate'_return [decidable_eq α] (x : α) :
  ⁅= x | simulate' so (return a) s⁆ = if x = a then 1 else 0 :=
by simp [simulate'_return, prob_output_return]

end prob_output

section prob_event

@[simp] lemma prob_event_simulate_return_eq_indicator (e : set (α × S)) :
  ⁅e | simulate so (return a) s⁆ = e.indicator (λ _, 1) (a, s) :=
prob_event_return_eq_indicator _ (a, s) e

@[simp] lemma prob_event_simulate_return (e : set (α × S)) [decidable_pred (∈ e)] :
  ⁅e | simulate so (return a) s⁆ = if (a, s) ∈ e then 1 else 0 :=
prob_event_return _ (a, s) e

@[simp] lemma prob_event_simulate'_return_eq_indicator (e : set α) :
  ⁅e | simulate' so (return a) s⁆ = e.indicator (λ _, 1) a :=
begin
  rw [prob_event_simulate', prob_event_simulate_return_eq_indicator],
  by_cases ha : a ∈ e,
  { have : (a, s) ∈ (prod.fst ⁻¹' e : set (α × S)) := ha,
    rw [set.indicator_of_mem ha, set.indicator_of_mem this] },
  { have : (a, s) ∉ (prod.fst ⁻¹' e : set (α × S)) := ha,
    rw [set.indicator_of_not_mem ha, set.indicator_of_not_mem this] }
end

@[simp] lemma prob_event_simulate'_return_eq_ite (e : set α) [decidable_pred (∈ e)] :
  ⁅e | simulate' so (return a) s⁆ = ite (a ∈ e) 1 0 :=
by {rw [prob_event_simulate'_return_eq_indicator, set.indicator], congr}

end prob_event

end oracle_comp