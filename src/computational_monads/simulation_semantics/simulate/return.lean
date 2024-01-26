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

-- namespace oracle_comp

-- open oracle_spec
-- open_locale big_operators ennreal

-- variables (so : sim_oracle spec spec' S) (a : α) (s : S)

-- section support

-- lemma support_simulate_return : (simulate so (return a) s).support = {(a, s)} := rfl

-- lemma mem_support_simulate_return_iff (x : α × S) :
--   x ∈ (simulate so (return a) s).support ↔ x.1 = a ∧ x.2 = s :=
-- prod.eq_iff_fst_eq_snd_eq

-- lemma mem_support_simulate_return_self : (a, s) ∈ (simulate so (return a) s).support :=
-- (mem_support_simulate_return_iff so a s (a, s)).2 ⟨rfl, rfl⟩

-- lemma support_simulate'_return : (simulate' so (return a) s).support = {a} := rfl

-- lemma mem_support_simulate'_return_iff (x : α) :
--   x ∈ (simulate' so (return a) s).support ↔ x = a := iff.rfl

-- lemma mem_support_simulate'_return_self : a ∈ (simulate' so (return a) s).support :=
-- (mem_support_simulate'_return_iff so a s a).2 rfl

-- end support

-- section fin_support

-- lemma fin_support_simulate_return [decidable_eq α] [decidable_eq S] :
--   (simulate so (return a) s).fin_support = {(a, s)} := rfl

-- lemma mem_fin_support_simulate_return_iff [decidable_eq α] [decidable_eq S] (x : α × S) :
--   x ∈ (simulate so (return a) s).fin_support ↔ x.1 = a ∧ x.2 = s :=
-- finset.mem_singleton.trans prod.eq_iff_fst_eq_snd_eq

-- lemma fin_support_simulate'_return [decidable_eq α] :
--   (simulate' so (return a) s).fin_support = {a} := rfl

-- lemma mem_fin_support_simulate'_return_iff [decidable_eq α] (x : α) :
--   x ∈ (simulate' so (return a) s).fin_support ↔ x = a := finset.mem_singleton

-- end fin_support

-- section eval_dist

-- lemma eval_dist_simulate_return : ⁅simulate so (return a) s⁆ = pmf.pure (a, s) := rfl

-- lemma eval_dist_simulate'_return : ⁅simulate' so (return a) s⁆ = pmf.pure a := by simp

-- end eval_dist

-- section dist_equiv

-- lemma simulate_return_dist_equiv' :
--   simulate so (return a) s ≃ₚ (return' !spec'! (a, s)) := refl _

-- lemma simulate_return_dist_equiv (spec'' : oracle_spec) :
--   simulate so (return a) s ≃ₚ (return' !spec''! (a, s)) := refl _

-- lemma simulate'_return_dist_equiv' : simulate' so (return a) s ≃ₚ (return' !spec'! a) :=
-- by pairwise_dist_equiv

-- lemma simulate'_return_dist_equiv (spec'' : oracle_spec) :
--   simulate' so (return a) s ≃ₚ (return' !spec''! a) :=
-- by simp [dist_equiv.ext_iff, simulate'_return, prob_output_return_eq_indicator]

-- end dist_equiv

-- section prob_output

-- lemma prob_output_simulate_return_eq_indicator (x : α × S) :
--   ⁅= x | simulate so (return a) s⁆ = set.indicator {(a, s)} (λ _, 1) x :=
-- prob_output_return_eq_indicator _ _ _

-- lemma prob_output_simulate_return [decidable_eq α] [decidable_eq S] (x : α × S) :
--   ⁅= x | simulate so (return a) s⁆ = if x = (a, s) then 1 else 0 :=
-- prob_output_return _ _ _

-- lemma prob_output_simulate'_return_eq_indicator (x : α) :
--   ⁅= x | simulate' so (return a) s⁆ = set.indicator {a} (λ _, 1) x :=
-- by simp [simulate'_return, prob_output_return_eq_indicator]

-- lemma prob_output_simulate'_return [decidable_eq α] (x : α) :
--   ⁅= x | simulate' so (return a) s⁆ = if x = a then 1 else 0 :=
-- by simp [simulate'_return, prob_output_return]

-- end prob_output

-- section prob_event

-- lemma prob_event_simulate_return (p : α × S → Prop) [decidable_pred p] :
--   ⁅p | simulate so (return a) s⁆ = if p (a, s) then 1 else 0 :=
-- prob_event_return _ (a, s) p

-- lemma prob_event_simulate'_return_eq_ite (p : α → Prop) [decidable_pred p] :
--   ⁅p | simulate' so (return a) s⁆ = if p a then 1 else 0 :=
-- by rw [simulate'_return, prob_event_return]

-- end prob_event

-- end oracle_comp