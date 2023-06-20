/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.return
import computational_monads.simulation_semantics.simulate.bind
/-!
# Distributional Semantics of Simulation of a Map Operation

This file contains lemmas about the computation `simulate so (f <$> oa) s`.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (f : α → β) (s : S)

section support


lemma support_simulate_map : (simulate so (f <$> oa) s).support =
  prod.map f id '' (simulate so oa s).support := by rw [simulate_map, support_map]


@[simp] lemma support_simulate'_map : (simulate' so (f <$> oa) s).support =
  f '' (simulate' so oa s).support :=
by simp only [simulate', support_map, support_simulate_map, set.image_image, prod.map_fst]



end support

section fin_support


end fin_support

section eval_dist


lemma eval_dist_simulate_map : ⁅simulate so (f <$> oa) s⁆ =
  ⁅simulate so oa s⁆.map (prod.map f id) := by rw [simulate_map, eval_dist_map]


@[simp] lemma eval_dist_simulate'_map : ⁅simulate' so (f <$> oa) s⁆ = ⁅simulate' so oa s⁆.map f :=
by simp_rw [eval_dist_simulate', eval_dist_simulate_map, pmf.map_comp, prod.map_fst']



end eval_dist

section dist_equiv


end dist_equiv

section prob_output


end prob_output

section prob_event


lemma prob_event_simulate_map (e : set (β × S)) :
  ⁅e | simulate so (f <$> oa) s⁆ = ⁅prod.map f id ⁻¹' e | simulate so oa s⁆ :=
by rw [simulate_map, prob_event_map]


lemma prob_event_simulate'_map (e : set β) :
  ⁅e | simulate' so (f <$> oa) s⁆ = ⁅(f ∘ prod.fst) ⁻¹' e | simulate so oa s⁆ :=
by simpa only [prob_event_simulate', prob_event_simulate_map, ← set.preimage_comp]


end prob_event

section indep_event


end indep_event

end oracle_comp