/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.basic

/-!
# Distributional Semantics of Simulation of a Query Operation

This file contains lemmas about the computation `simulate so (query i t) s`.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables (so : sim_oracle spec spec' S) (i : spec.ι) (t : spec.domain i) (s : S)

section support


lemma support_simulate_query : (simulate so (query i t) s).support = (so i (t, s)).support := rfl


lemma support_simulate'_query : (simulate' so (query i t) s).support =
  prod.fst '' (so i (t, s)).support := by simp only [simulate'_query, support_map]


end support

section fin_support


end fin_support

section eval_dist


lemma eval_dist_simulate_query : ⁅simulate so (query i t) s⁆ = ⁅so i (t, s)⁆ := rfl


lemma eval_dist_simulate'_query : ⁅simulate' so (query i t) s⁆ = ⁅so i (t, s)⁆.map prod.fst :=
by simp only [simulate'_query, eval_dist_map]


end eval_dist

section dist_equiv


end dist_equiv

section prob_output


end prob_output

section prob_event


lemma prob_event_simulate_query (e : set (spec.range i × S)) :
  ⁅e | simulate so (query i t) s⁆ = ⁅e | so i (t, s)⁆ := rfl


lemma prob_event_simulate'_query (e : set (spec.range i)) :
  ⁅e | simulate' so (query i t) s⁆ = ⁅prod.fst ⁻¹' e | so i (t, s)⁆ :=
by rw [prob_event_simulate', prob_event_simulate_query]


end prob_event

section indep_event


end indep_event

end oracle_comp