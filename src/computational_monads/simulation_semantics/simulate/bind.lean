/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.basic

/-!
# Distributional Semantics of Simulation of a Bind Operation

This file contains lemmas about the computation `simulate so (oa >>= ob) s`.
-/

variables {α β γ : Type} {spec spec' : oracle_spec} {S : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables (so : sim_oracle spec spec' S) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (s : S)

section support

@[simp] lemma support_simulate_bind : (simulate so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma mem_support_simulate_bind_iff (y : β × S) : y ∈ (simulate so (oa >>= ob) s).support ↔
  ∃ a s', (a, s') ∈ (simulate so oa s).support ∧ y ∈ (simulate so (ob a) s').support :=
by simp_rw [support_simulate_bind, set.mem_Union, prod.exists, exists_prop]

lemma mem_support_simulate_bind_iff' (y : β × S) : y ∈ (simulate so (oa >>= ob) s).support ↔
  ∃ x, x ∈ (simulate so oa s).support ∧ y ∈ (simulate so (ob (prod.fst x)) x.2).support :=
by simp_rw [support_simulate_bind, set.mem_Union, exists_prop]

@[simp] lemma support_simulate'_bind : (simulate' so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
by simp [set.image_Union]

lemma mem_support_simulate'_bind_iff (x : β) : x ∈ (simulate' so (oa >>= ob) s).support ↔
  ∃ a s', (a, s') ∈ (simulate so oa s).support ∧ x ∈ (simulate' so (ob a) s').support :=
by simp [simulate'_bind, support_map_bind, set.mem_Union, support_simulate']

end support

section eval_dist

@[simp] lemma eval_dist_simulate_bind : ⁅simulate so (oa >>= ob) s⁆ =
  (⁅simulate so oa s⁆).bind (λ x, ⁅simulate so (ob x.1) x.2⁆) :=
(congr_arg _ $ simulate_bind so oa ob s).trans (eval_dist_bind _ _)

@[simp] lemma eval_dist_simulate'_bind : ⁅simulate' so (oa >>= ob) s⁆ =
  ⁅simulate so oa s⁆.bind (λ x, ⁅simulate' so (ob x.1) x.2⁆) :=
by simp only [simulate'_bind, eval_dist_map_bind, eval_dist_bind, eval_dist_map,
  eval_dist_simulate', eq_self_iff_true, pmf.map_bind]

end eval_dist

section dist_equiv

lemma simulate_bind_dist_equiv : simulate so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := refl _

lemma simulate'_bind_dist_equiv : simulate' so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 := by pairwise_dist_equiv

lemma simulate_bind_dist_equiv_simulate'_bind
  (oz : α × S → oracle_comp spec' β) (s₀ s : S) (h : ∀ z, oz z ≃ₚ oz (z.1, s)) :
  simulate so oa s₀ >>= oz ≃ₚ simulate' so oa s₀ >>= λ x, oz (x, s) :=
bind_dist_equiv_fst_bind _ _ _ h

end dist_equiv

section prob_output

/-- Write the `eval_dist` of a simulation as a double summation over the possible
intermediate outputs and states of the computation. -/
@[simp] lemma prob_output_simulate_bind_eq_tsum_tsum (x : β × S) :
  ⁅= x | simulate so (oa >>= ob) s⁆ =
    ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= x | simulate so (ob a) s'⁆ :=
by rw [simulate_bind, prob_output_prod_bind]

@[simp] lemma prob_output_simulate_bind_eq_sum_sum [fintype α] [fintype S] (x : β × S) :
  ⁅= x | simulate so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= x | simulate so (ob a) s'⁆ :=
by simp only [simulate_bind, prob_output_bind_eq_sum, ← @finset.sum_product ℝ≥0∞ S α _
  finset.univ finset.univ (λ y, ⁅= (y.1, y.2) | simulate so oa s⁆ * ⁅= x | simulate so (ob y.1) y.2⁆),
  finset.univ_product_univ, prod.mk.eta]

@[simp] lemma prob_output_simulate'_bind_eq_tsum_tsum (b : β) : ⁅= b | simulate' so (oa >>= ob) s⁆
  = ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= b | simulate' so (ob a) s'⁆ :=
by simp only [prob_output_simulate'_eq_prob_event, simulate_bind,
  prob_event_bind_eq_tsum, ← ennreal.tsum_prod, prod.mk.eta]

@[simp] lemma prob_output_simulate'_bind_eq_sum_sum [fintype α] [fintype S] (b : β) :
  ⁅= b | simulate' so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= b | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_output_simulate'_bind_eq_tsum_tsum, tsum_fintype]

end prob_output

section prob_event

@[simp] lemma prob_event_simulate_bind_eq_tsum_tsum (e : set (β × S)) :
  ⁅e | simulate so (oa >>= ob) s⁆ =
    ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate so (ob a) s'⁆ :=
by simp_rw [simulate_bind, prob_event_bind_eq_tsum, ← ennreal.tsum_prod, prod.mk.eta]

lemma prob_event_simulate_bind_eq_sum_sum [fintype α] [fintype S] (e : set (β × S)) :
  ⁅e | simulate so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate so (ob a) s'⁆ :=
by simp only [simulate_bind, prob_event_bind_eq_sum, ← @finset.sum_product ℝ≥0∞ S α _ finset.univ
  finset.univ (λ x, ⁅= (x.1, x.2) | simulate so oa s⁆ * ⁅e | simulate so (ob x.1) x.2⁆),
  finset.univ_product_univ, prod.mk.eta]

@[simp] lemma prob_event_simulate'_bind_eq_tsum_tsum (e : set β) :
  ⁅e | simulate' so (oa >>= ob) s⁆ =
    ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_event_simulate', prob_event_simulate_bind_eq_tsum_tsum]

lemma prob_event_simulate'_bind_eq_sum_sum [fintype α] [fintype S] (e : set β) :
  ⁅e | simulate' so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_event_simulate', prob_event_simulate_bind_eq_sum_sum]

end prob_event

end oracle_comp