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

TODO: might be fine to get rid of these kinds of files
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (f : α → β) (s : S)

section support

@[simp] lemma support_simulate_map : (simulate so (f <$> oa) s).support =
  prod.map f id '' (simulate so oa s).support := by rw [simulate_map, support_map]

lemma mem_support_simulate_map_iff (y : β × S) : y ∈ (simulate so (f <$> oa) s).support ↔
  ∃ x, (x, y.2) ∈ (simulate so oa s).support ∧ f x = y.1 :=
by simp only [simulate_map, support_map, set.image, prod.eq_iff_fst_eq_snd_eq, prod_map, id.def,
  prod.exists, exists_eq_right_right, set.mem_set_of_eq]

@[simp] lemma support_simulate'_map : (simulate' so (f <$> oa) s).support =
  f '' (simulate' so oa s).support :=
by simp only [simulate', support_map, support_simulate_map, set.image_image, prod.map_fst]

lemma mem_support_simulate'_map_iff (y : β) : y ∈ (simulate' so (f <$> oa) s).support ↔
  ∃ x s', (x, s') ∈ (simulate so oa s).support ∧ f x = y :=
by simp_rw [simulate'_map, support_map, set.mem_image, mem_support_simulate'_iff_exists_state,
  exists_and_distrib_right]

end support

section eval_dist

@[simp] lemma eval_dist_simulate_map : ⁅simulate so (f <$> oa) s⁆ =
  ⁅simulate so oa s⁆.map (prod.map f id) := by rw [simulate_map, eval_dist_map]

@[simp] lemma eval_dist_simulate'_map : ⁅simulate' so (f <$> oa) s⁆ = ⁅simulate' so oa s⁆.map f :=
by simp_rw [eval_dist_simulate', eval_dist_simulate_map, pmf.map_comp, prod.map_fst']

end eval_dist

section dist_equiv

@[pairwise_dist_equiv] lemma simulate_map_dist_equiv :
  simulate so (f <$> oa) s ≃ₚ (prod.map f id) <$> simulate so oa s := by rw [simulate_map]

lemma simulate'_map_dist_equiv : simulate' so (f <$> oa) s ≃ₚ f <$> simulate' so oa s :=
by simp [dist_equiv.def, pmf.map_comp, prod.map_fst']

end dist_equiv

section prob_output

@[simp] lemma prob_output_simulate_map [decidable_eq S] [decidable_eq β]
  (y : β × S) : ⁅= y | simulate so (f <$> oa) s⁆ =
    ∑' x, if y.1 = f x then ⁅= (x, y.snd) | simulate so oa s⁆ else 0 :=
by rw [simulate_map, prob_output_map_prod_map_id_right]

@[simp] lemma prob_output_simulate'_map [decidable_eq β]
  (y : β) : ⁅= y | simulate' so (f <$> oa) s⁆ =
    ∑' x, if y = f x then ⁅= x | simulate' so oa s⁆ else 0 :=
by rw [simulate'_map, prob_output_map_eq_tsum_ite]

end prob_output

section prob_event

@[simp] lemma prob_event_simulate_map (e : β × S → Prop) :
  ⁅e | simulate so (f <$> oa) s⁆ = ⁅e ∘ prod.map f id | simulate so oa s⁆ :=
by rw [simulate_map, prob_event_map]

@[simp] lemma prob_event_simulate'_map (e : β → Prop) :
  ⁅e | simulate' so (f <$> oa) s⁆ = ⁅e ∘ f ∘ prod.fst | simulate so oa s⁆ :=
by simpa only [prob_event_simulate', prob_event_simulate_map, ← set.preimage_comp]

end prob_event

end oracle_comp