/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.eval_dist

/-!
# Probability of Events

This file defines the probability of some event holding after running a computation.
The definition is in terms of the `measure` associated to the `pmf` given by `eval_dist`.

This definition is equivalent to one in terms of summations, in particular an infinite `tsum`.
If the support is decidable (or the event is a `finset`),
we can instead give an expression in terms of `finset.sum`.
-/

namespace distribution_semantics

open oracle_comp oracle_spec
open_locale classical big_operators ennreal

variables {α β γ : Type} {spec : oracle_spec} [finite_range spec] (a a' : α)
  (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) (f : α → β) (g : β → γ) (e : set α) (e' : set β)

/-- Probability of a predicate holding after running a particular experiment.
Defined in terms of the outer measure associated to the corresponding `pmf` by `eval_dist`. -/
noncomputable def prob_event (oa : oracle_comp spec α) (event : set α) : ℝ≥0∞ :=
⦃oa⦄.to_outer_measure event

notation `⦃` event `|` oa `⦄` := prob_event oa event

lemma prob_event.def : ⦃e | oa⦄ = ⦃oa⦄.to_outer_measure e := rfl

lemma prob_event_eq_to_measure_apply : ⦃e | oa⦄ = (@pmf.to_measure α ⊤ ⦃oa⦄ e) :=
(@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ ⦃oa⦄ e
  measurable_space.measurable_set_top).symm

lemma prob_event_le_one : ⦃e | oa⦄ ≤ 1 :=
(⦃oa⦄.to_outer_measure.mono (set.subset_univ e)).trans
  (le_of_eq $ (⦃oa⦄.to_outer_measure_apply_eq_one_iff _).2 (set.subset_univ ⦃oa⦄.support))

/-- Probability of an event in terms of non-decidable `set.indicator` sum -/
lemma prob_event_eq_tsum_indicator : ⦃e | oa⦄ = ∑' x, e.indicator ⦃oa⦄ x :=
pmf.to_outer_measure_apply ⦃oa⦄ e

/-- Probability of an event in terms of a decidable `ite` sum-/
lemma prob_event_eq_tsum_ite [decidable_pred (∈ e)] : ⦃e | oa⦄ = ∑' x, ite (x ∈ e) (⦃oa⦄ x) 0 :=
(prob_event_eq_tsum_indicator oa e).trans (tsum_congr $ λ x, by {unfold set.indicator, congr})

lemma prob_event_finset_eq_sum (e : finset α) : ⦃↑e | oa⦄ = ∑ x in e, ⦃oa⦄ x :=
by rw [prob_event_eq_tsum_indicator, finset.sum_eq_tsum_indicator]

/-- If the intersection of a set `e'` contains all elements of `e` that have non-zero
probability under `⦃oa⦄` then the probability of `e'` is at least as big as that of `e`. -/
lemma prob_event_mono {e e'} (h : (e ∩ oa.support) ⊆ e') : ⦃e | oa⦄ ≤ ⦃e' | oa⦄ :=
pmf.to_outer_measure_mono ⦃oa⦄ (by simpa only [support_eval_dist])

lemma prob_event_mono' {e e'} (h : e ⊆ e') : ⦃e | oa⦄ ≤ ⦃e' | oa⦄ :=
prob_event_mono oa (trans (set.inter_subset_left _ _) h)

lemma prob_event_le_of_eval_dist_apply_le {oa oa' : oracle_comp spec α}
  (h : ∀ x ∈ oa.support, ⦃oa⦄ x ≤ ⦃oa'⦄ x) (e : set α) : ⦃e | oa⦄ ≤ ⦃e | oa'⦄ :=
begin
  simp only [prob_event_eq_tsum_indicator],
  refine ennreal.tsum_le_tsum (λ x, _),
  refine set.indicator_apply_le (λ hxe, _),
  by_cases hx : x ∈ oa.support,
  { rw [(set.indicator_apply_eq_self.2 $ λ hxe', (hxe' hxe).elim)],
    exact h x hx },
  { simp only [eval_dist_eq_zero_of_not_mem_support hx, zero_le'] }
end

/-- If the `eval_dist` agrees on all elements of the support, then `prob_event` agrees as well. -/
lemma prob_event_eq_of_eval_dist_apply_eq {oa oa' : oracle_comp spec α}
  (h : ∀ x ∈ oa.support ∪ oa'.support, ⦃oa⦄ x = ⦃oa'⦄ x) (e : set α) : ⦃e | oa⦄ = ⦃e | oa'⦄ :=
antisymm (prob_event_le_of_eval_dist_apply_le (λ x hx, le_of_eq (h x $ or.inl hx)) e)
  (prob_event_le_of_eval_dist_apply_le (λ x hx, le_of_eq (h x $ or.inr hx).symm) e)

lemma prob_event_eq_of_eval_dist_eq {oa oa' : oracle_comp spec α}
  (h : ⦃oa⦄ = ⦃oa'⦄) (e : set α) : ⦃e | oa⦄ = ⦃e | oa'⦄ :=
prob_event_eq_of_eval_dist_apply_eq (λ x _, by rw [h]) e

section return

@[simp] lemma prob_event_return : ⦃e | (return a : oracle_comp spec α)⦄ = ite (a ∈ e) 1 0 :=
by simp only [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply]

lemma prob_event_return_eq_indicator : ⦃e | (return a : oracle_comp spec α)⦄ =
  e.indicator (λ _, 1) a := by simp only [prob_event_return, set.indicator_apply]

lemma prob_event_return_of_true (ha : a ∈ e) : ⦃e | (return a : oracle_comp spec α)⦄ = 1 :=
by simp only [ha, prob_event_return_eq_indicator, set.indicator_of_mem]

lemma prob_event_return_of_false (ha : a ∉ e) : ⦃e | (return a : oracle_comp spec α)⦄ = 0 :=
by simp only [ha, prob_event_return_eq_indicator, set.indicator_of_not_mem, not_false_iff]

end return

section bind

@[simp] lemma prob_event_bind : ⦃e' | oa >>= ob⦄ = ∑' (a : α), ⦃oa⦄ a * ⦃e' | ob a⦄ :=
by simp only [prob_event.def, eval_dist_bind, pmf.to_outer_measure_bind_apply]

@[simp] lemma prob_event_return_bind : ⦃e' | return a >>= ob⦄ = ⦃e' | ob a⦄ :=
prob_event_eq_of_eval_dist_eq (eval_dist_return_bind a ob) e'

@[simp] lemma prob_event_bind_return : ⦃e | oa >>= return⦄ = ⦃e | oa⦄ :=
prob_event_eq_of_eval_dist_eq (eval_dist_bind_return_id oa) e

end bind

section query

@[simp] lemma prob_event_query (e : set $ spec.range i) :
  ⦃e | query i t⦄ = fintype.card e / fintype.card (spec.range i) :=
by simp only [prob_event.def, eval_dist_query, pmf.to_outer_measure_uniform_of_fintype_apply,
  fintype.card_of_finset, finset.filter_congr_decidable]

@[simp] lemma prob_event_query_bind (oa : spec.range i → oracle_comp spec α) :
  ⦃e | query i t >>= oa⦄ = (∑' x, ⦃e | oa x⦄) / fintype.card (spec.range i) :=
by simp only [prob_event_bind, eval_dist_query_apply, div_eq_mul_inv,
  ← ennreal.tsum_mul_right, one_mul, mul_comm]

end query

section map

@[simp] lemma prob_event_map : ⦃e' | f <$> oa⦄ = ⦃f ⁻¹' e' | oa⦄ :=
by simp only [prob_event.def, eval_dist_map, pmf.to_outer_measure_map_apply]

end map

section support

/-- If two sets have the same intersection with the support of a computation,
then they both have the same probability under `prob_event` -/
lemma prob_event_eq_prob_event_of_inter_support_eq {e e'}
  (h : e ∩ oa.support = e' ∩ oa.support) : ⦃e | oa⦄ = ⦃e' | oa⦄ :=
pmf.to_outer_measure_apply_eq_of_inter_support_eq ⦃oa⦄ (by simpa only [support_eval_dist])

/-- Probability can be calculated on only the intersection of the set with the support. -/
lemma prob_event_eq_prob_event_inter_support : ⦃e | oa⦄ = ⦃e ∩ oa.support | oa⦄ :=
prob_event_eq_prob_event_of_inter_support_eq oa (by rw [set.inter_assoc, set.inter_self])

/-- Given a `finset` containing the `support` of some `oracle_comp`,
  it suffices to take `finset.sum` over that instead of a `tsum` -/
theorem prob_event_eq_sum_of_support_subset (s : finset α) (hs : oa.support ⊆ s) :
  ⦃e | oa⦄ = ∑ x in s, if x ∈ e then ⦃oa⦄ x else 0 :=
trans (prob_event_eq_tsum_ite oa e) (tsum_eq_sum (λ x hx,
  by rw [eval_dist_eq_zero_of_not_mem_support (λ hx', hx $ finset.mem_coe.1 (hs hx')), if_t_t]))

theorem prob_event_bind_eq_sum_of_support_subset (e : set β) (s : finset α) (hs : oa.support ⊆ s) :
  ⦃e | oa >>= ob⦄ = ∑ x in s, ⦃oa⦄ x * ⦃e | ob x⦄ :=
trans (prob_event_bind oa ob e) (tsum_eq_sum (λ x hx,
  by rw [eval_dist_eq_zero_of_not_mem_support (λ h, hx (hs h)), zero_mul]))

@[simp] lemma prob_event_eq_zero_iff_disjoint_support : ⦃e | oa⦄ = 0 ↔ disjoint oa.support e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_zero_iff, support_eval_dist]

@[simp] lemma prob_event_eq_one_iff_support_subset : ⦃e | oa⦄ = 1 ↔ oa.support ⊆ e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_one_iff, support_eval_dist]

end support

section fin_support

variables [computable spec] [decidable oa]

lemma prob_event_eq_sum_fin_support :
  ⦃e | oa⦄ = ∑ x in oa.fin_support, if x ∈ e then ⦃oa⦄ x else 0 :=
(prob_event_eq_sum_of_support_subset _ e oa.fin_support $ support_subset_coe_fin_support oa)

end fin_support

lemma prob_event_eq_eval_dist_of_disjoint_sdiff_support {x : α}
  (hx : x ∈ e) (h : disjoint (e \ {x}) oa.support) : ⦃e | oa⦄ = ⦃oa⦄ x :=
⦃oa⦄.to_outer_measure_apply_eq_apply e x hx (by rwa [support_eval_dist])

lemma prob_event_Union_eq_of_pairwise_disjoint (es : ℕ → set α) (h : pairwise (disjoint on es)) :
  ⦃⋃ i, es i | oa⦄ = ∑' i, ⦃es i | oa⦄ :=
by simp only [prob_event.def, pmf.to_outer_measure_apply_Union ⦃oa⦄ h]

lemma prob_event_union_eq_of_disjoint {e e' : set α} --[decidable_pred e] [decidable_pred e']
  (h : disjoint e e') : ⦃e ∪ e' | oa⦄ = ⦃e | oa⦄ + ⦃e' | oa⦄ :=
begin
  simp only [prob_event_eq_to_measure_apply],
  exact @measure_theory.measure_union α ⊤ _ e e' h measurable_space.measurable_set_top,
end

lemma prob_event_eq_prob_event_inter_add_prob_event_diff {e s : set α} :
  ⦃e | oa⦄ = ⦃e ∩ s | oa⦄ + ⦃e \ s | oa⦄ :=
trans (by rw [set.inter_union_diff]) (prob_event_union_eq_of_disjoint oa $
  set.disjoint_of_subset_left (set.inter_subset_right _ _) (set.disjoint_diff))

end distribution_semantics