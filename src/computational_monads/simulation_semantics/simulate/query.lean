/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.basic
import computational_monads.distribution_semantics.query

/-!
# Distributional Semantics of Simulation of a Query Operation

This file contains lemmas about the computation `simulate so (query i t) s`.
-/

variables {α β γ : Type} {spec spec' : oracle_spec} {S : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables (so : sim_oracle spec spec' S) (i : spec.ι) (t : spec.domain i) (s : S)

section support

@[simp] lemma support_simulate_query :
  (simulate so (query i t) s).support = (so i (t, s)).support := rfl

lemma mem_support_simulate_query_iff (z : spec.range i × S) :
  z ∈ (simulate so (query i t) s).support ↔ z ∈ (so i (t, s)).support := iff.rfl

lemma support_simulate'_query : (simulate' so (query i t) s).support =
  prod.fst '' (so i (t, s)).support := by simp

lemma mem_support_simulate'_query_iff (u : spec.range i) :
  u ∈ (simulate' so (query i t) s).support ↔ ∃ s', (u, s') ∈ (so i (t, s)).support :=
by simp only [support_simulate', support_simulate_query, set.mem_image, prod.exists,
  exists_and_distrib_right, exists_eq_right]

end support

section fin_support

@[simp] lemma fin_support_simulate_query :
  (simulate so (query i t) s).fin_support = (so i (t, s)).fin_support := rfl

@[simp] lemma fin_support_simulate'_query [decidable_eq S] :
  (simulate' so (query i t) s).fin_support = (so i (t, s)).fin_support.image prod.fst := by simp

end fin_support

section eval_dist

@[simp] lemma eval_dist_simulate_query :
  ⁅simulate so (query i t) s⁆ = ⁅so i (t, s)⁆ := rfl

@[simp] lemma eval_dist_simulate'_query :
  ⁅simulate' so (query i t) s⁆ = ⁅so i (t, s)⁆.map prod.fst :=
by simp only [simulate'_query, eval_dist_map]

end eval_dist

section dist_equiv

@[simp, simp_dist_equiv] lemma simulate_query_dist_equiv :
  simulate so (query i t) s ≃ₚ so i (t, s) := by pairwise_dist_equiv

@[simp, simp_dist_equiv] lemma simulate'_query_dist_equiv :
  simulate' so (query i t) s ≃ₚ prod.fst <$> so i (t, s) := by pairwise_dist_equiv

end dist_equiv

section prob_output

@[simp] lemma prob_output_simulate_query (x : spec.range i × S) :
  ⁅= x | simulate so (query i t) s⁆ = ⁅= x | so i (t, s)⁆ := rfl

@[simp] lemma prob_output_simulate'_query_eq_tsum (x : spec.range i) :
  ⁅= x | simulate' so (query i t) s⁆ = ∑' s', ⁅= (x, s') | so i (t, s)⁆ :=
by simp only [prob_output_simulate', prob_output_simulate_query]

end prob_output

section prob_event

@[simp] lemma prob_event_simulate_query (e : set (spec.range i × S)) :
  ⁅e | simulate so (query i t) s⁆ = ⁅e | so i (t, s)⁆ := rfl

@[simp] lemma prob_event_simulate'_query (e : set (spec.range i)) :
  ⁅e | simulate' so (query i t) s⁆ = ⁅prod.fst ⁻¹' e | so i (t, s)⁆ :=
by rw [prob_event_simulate', prob_event_simulate_query]

end prob_event

end oracle_comp