/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.basic
import computational_monads.distribution_semantics.query

/-!
# Distribution Semantics of Simulated Computations

This file contains lemmas about the interactions between `simulate` and monadic operations.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

section return

variables (so : sim_oracle spec spec' S) (a : α) (s : S)

lemma support_simulate_return : (simulate so (return a) s).support = {(a, s)} := rfl

lemma mem_support_simulate_return_iff (x : α × S) :
  x ∈ (simulate so (return a) s).support ↔ x.1 = a ∧ x.2 = s :=
prod.eq_iff_fst_eq_snd_eq

lemma mem_support_simulate_return_self : (a, s) ∈ (simulate so (return a) s).support :=
(mem_support_simulate_return_iff so a s (a, s)).2 ⟨rfl, rfl⟩

lemma support_simulate'_return : (simulate' so (return a) s).support = {a} := rfl

lemma mem_support_simulate'_return_iff (x : α) :
  x ∈ (simulate' so (return a) s).support ↔ x = a := iff.rfl

lemma mem_support_simulate'_return_self : a ∈ (simulate' so (return a) s).support :=
(mem_support_simulate'_return_iff so a s a).2 rfl

lemma fin_support_simulate_return [decidable_eq α] [decidable_eq S] :
  (simulate so (return a) s).fin_support = {(a, s)} := rfl

lemma mem_fin_support_simulate_return_iff [decidable_eq α] [decidable_eq S] (x : α × S) :
  x ∈ (simulate so (return a) s).fin_support ↔ x.1 = a ∧ x.2 = s :=
finset.mem_singleton.trans prod.eq_iff_fst_eq_snd_eq

lemma fin_support_simulate'_return [decidable_eq α] :
  (simulate' so (return a) s).fin_support = {a} := rfl

lemma mem_fin_support_simulate'_return_iff [decidable_eq α] (x : α) :
  x ∈ (simulate' so (return a) s).fin_support ↔ x = a := finset.mem_singleton

lemma eval_dist_simulate_return : ⁅simulate so (return a) s⁆ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate'_return : ⁅simulate' so (return a) s⁆ = pmf.pure a := by simp

lemma simulate_return_dist_equiv' :
  simulate so (return a) s ≃ₚ (return' !spec'! (a, s)) := refl _

lemma simulate_return_dist_equiv (spec'' : oracle_spec) :
  simulate so (return a) s ≃ₚ (return' !spec''! (a, s)) := refl _

lemma simulate'_return_dist_equiv' : simulate' so (return a) s ≃ₚ (return' !spec'! a) :=
by pairwise_dist_equiv

lemma simulate'_return_dist_equiv (spec'' : oracle_spec) :
  simulate' so (return a) s ≃ₚ (return' !spec''! a) :=
by simp [dist_equiv.ext_iff, simulate'_return, prob_output_return_eq_indicator]

lemma prob_output_simulate_return_eq_indicator (x : α × S) :
  ⁅= x | simulate so (return a) s⁆ = set.indicator {(a, s)} (λ _, 1) x :=
prob_output_return_eq_indicator _ _ _

lemma prob_output_simulate_return [decidable_eq α] [decidable_eq S] (x : α × S) :
  ⁅= x | simulate so (return a) s⁆ = if x = (a, s) then 1 else 0 :=
prob_output_return _ _ _

lemma prob_output_simulate'_return_eq_indicator (x : α) :
  ⁅= x | simulate' so (return a) s⁆ = set.indicator {a} (λ _, 1) x :=
by simp [simulate'_return, prob_output_return_eq_indicator]

lemma prob_output_simulate'_return [decidable_eq α] (x : α) :
  ⁅= x | simulate' so (return a) s⁆ = if x = a then 1 else 0 :=
by simp [simulate'_return, prob_output_return]

lemma prob_event_simulate_return (p : α × S → Prop) [decidable_pred p] :
  ⁅p | simulate so (return a) s⁆ = if p (a, s) then 1 else 0 :=
prob_event_return _ (a, s) p

lemma prob_event_simulate'_return_eq_ite (p : α → Prop) [decidable_pred p] :
  ⁅p | simulate' so (return a) s⁆ = if p a then 1 else 0 :=
by rw [simulate'_return, prob_event_return]

end return

section bind

variables (so : sim_oracle spec spec' S) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (s : S)

lemma support_simulate_bind : (simulate so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support :=
by rw [simulate_bind, support_bind]

lemma mem_support_simulate_bind_iff (y : β × S) : y ∈ (simulate so (oa >>= ob) s).support ↔
  ∃ a s', (a, s') ∈ (simulate so oa s).support ∧ y ∈ (simulate so (ob a) s').support :=
by simp_rw [support_simulate_bind, set.mem_Union, prod.exists, exists_prop]

lemma mem_support_simulate_bind_iff' (y : β × S) : y ∈ (simulate so (oa >>= ob) s).support ↔
  ∃ x, x ∈ (simulate so oa s).support ∧ y ∈ (simulate so (ob (prod.fst x)) x.2).support :=
by simp_rw [support_simulate_bind, set.mem_Union, exists_prop]

lemma support_simulate'_bind : (simulate' so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
by simp

lemma mem_support_simulate'_bind_iff (x : β) : x ∈ (simulate' so (oa >>= ob) s).support ↔
  ∃ a s', (a, s') ∈ (simulate so oa s).support ∧ x ∈ (simulate' so (ob a) s').support :=
by simp [simulate'_bind, support_map, set.mem_Union, support_simulate']

lemma eval_dist_simulate_bind : ⁅simulate so (oa >>= ob) s⁆ =
  (⁅simulate so oa s⁆).bind (λ x, ⁅simulate so (ob x.1) x.2⁆) :=
(congr_arg _ $ simulate_bind so oa ob s).trans (eval_dist_bind _ _)

lemma eval_dist_simulate'_bind : ⁅simulate' so (oa >>= ob) s⁆ =
  ⁅simulate so oa s⁆.bind (λ x, ⁅simulate' so (ob x.1) x.2⁆) :=
by simp only [simulate'_bind, eval_dist_bind, eval_dist_map,
  eval_dist_simulate', eq_self_iff_true, pmf.map_bind]

@[pairwise_dist_equiv] lemma simulate_bind_dist_equiv : simulate so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := by simp [simulate_bind]

@[pairwise_dist_equiv] lemma simulate'_bind_dist_equiv : simulate' so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 := by simp [simulate'_bind]

lemma simulate_bind_dist_equiv_simulate'_bind
  (oz : α × S → oracle_comp spec' β) (s₀ s : S) (h : ∀ z, oz z ≃ₚ oz (z.1, s)) :
  simulate so oa s₀ >>= oz ≃ₚ simulate' so oa s₀ >>= λ x, oz (x, s) :=
bind_dist_equiv_fst_bind _ _ _ h

/-- Write the `eval_dist` of a simulation as a double summation over the possible
intermediate outputs and states of the computation. -/
lemma prob_output_simulate_bind_eq_tsum_tsum (x : β × S) :
  ⁅= x | simulate so (oa >>= ob) s⁆ =
    ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= x | simulate so (ob a) s'⁆ :=
by simp [prob_output_prod_bind] -- rw [simulate_bind, prob_output_prod_bind]

lemma prob_output_simulate_bind_eq_sum_sum [fintype α] [fintype S] (x : β × S) :
  ⁅= x | simulate so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= x | simulate so (ob a) s'⁆ :=
by simp only [simulate_bind, prob_output_bind_eq_sum_fintype, ← @finset.sum_product ℝ≥0∞ S α _
  finset.univ finset.univ (λ y, ⁅= (y.1, y.2) | simulate so oa s⁆ *
    ⁅= x | simulate so (ob y.1) y.2⁆),
  finset.univ_product_univ, prod.mk.eta]

lemma prob_output_simulate'_bind_eq_tsum_tsum (b : β) : ⁅= b | simulate' so (oa >>= ob) s⁆
  = ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= b | simulate' so (ob a) s'⁆ :=
by simp only [prob_output_simulate'_eq_prob_event_simulate, simulate_bind,
  prob_event_bind_eq_tsum, ← ennreal.tsum_prod, prod.mk.eta]

lemma prob_output_simulate'_bind_eq_sum_sum [fintype α] [fintype S] (b : β) :
  ⁅= b | simulate' so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= b | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_output_simulate'_bind_eq_tsum_tsum, tsum_fintype]

lemma prob_event_simulate_bind_eq_tsum_tsum (e : β × S → Prop) :
  ⁅e | simulate so (oa >>= ob) s⁆ =
    ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate so (ob a) s'⁆ :=
by simp_rw [simulate_bind, prob_event_bind_eq_tsum, ← ennreal.tsum_prod, prod.mk.eta]

lemma prob_event_simulate_bind_eq_sum_sum [fintype α] [fintype S] (e : β × S → Prop) :
  ⁅e | simulate so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate so (ob a) s'⁆ :=
by simp only [simulate_bind, prob_event_bind_eq_sum_fintype,
  ← @finset.sum_product ℝ≥0∞ S α _ finset.univ
  finset.univ (λ x, ⁅= (x.1, x.2) | simulate so oa s⁆ * ⁅e | simulate so (ob x.1) x.2⁆),
  finset.univ_product_univ, prod.mk.eta]

lemma prob_event_simulate'_bind_eq_tsum_tsum (e : β → Prop) :
  ⁅e | simulate' so (oa >>= ob) s⁆ =
    ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_event_simulate', prob_event_simulate_bind_eq_tsum_tsum]

lemma prob_event_simulate'_bind_eq_sum_sum [fintype α] [fintype S] (e : β → Prop) :
  ⁅e | simulate' so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_event_simulate', prob_event_simulate_bind_eq_sum_sum]

end bind

end oracle_comp