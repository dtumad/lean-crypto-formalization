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
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Probability of a predicate holding after running a particular experiment.
Defined in terms of the outer measure associated to the corresponding `pmf` by `eval_dist`. -/
noncomputable def prob_event (oa : oracle_comp spec α) (event : set α) : ℝ≥0∞ :=
⁅oa⁆.to_outer_measure event

notation `⁅` event `|` oa `⁆` := prob_event oa event

lemma prob_event.def (oa : oracle_comp spec α) (event : set α) :
  ⁅event | oa⁆ = ⁅oa⁆.to_outer_measure event := rfl

lemma prob_event_eq_to_measure_apply (oa : oracle_comp spec α) (event : set α) :
  ⁅event | oa⁆ = (@pmf.to_measure α ⊤ ⁅oa⁆ event) :=
(@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ ⁅oa⁆ event
  measurable_space.measurable_set_top).symm

lemma prob_event_singleton_eq_eval_dist (oa : oracle_comp spec α) (x : α) :
  ⁅{x} | oa⁆ = ⁅oa⁆ x := by rw [prob_event.def, pmf.to_outer_measure_apply_singleton]

lemma prob_event_eq_eq_eval_dist (oa : oracle_comp spec α) (x : α) :
  ⁅(=) x | oa⁆ = ⁅oa⁆ x :=
trans (congr_arg (λ s, ⁅s | oa⁆) (set.ext $ λ y, eq_comm)) (prob_event_singleton_eq_eval_dist oa x)

section sums

variables (oa : oracle_comp spec α) (e : set α)

/-- Probability of an event in terms of non-decidable `set.indicator` sum -/
lemma prob_event_eq_tsum_indicator : ⁅e | oa⁆ = ∑' x, e.indicator ⁅oa⁆ x :=
pmf.to_outer_measure_apply ⁅oa⁆ e

lemma prob_event_eq_sum_indicator [fintype α] : ⁅e | oa⁆ = ∑ x, e.indicator ⁅oa⁆ x :=
(prob_event_eq_tsum_indicator oa e).trans (tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim))

lemma prob_event_eq_sum_fin_support_indicator [oa.decidable] :
  ⁅e | oa⁆ = ∑ x in oa.fin_support, e.indicator ⁅oa⁆ x :=
(prob_event_eq_tsum_indicator oa e).trans (tsum_eq_sum $ λ a ha,
  set.indicator_apply_eq_zero.2 (λ _, eval_dist_eq_zero_of_not_mem_fin_support ha))

/-- Probability of an event in terms of a decidable `ite` sum-/
lemma prob_event_eq_tsum_ite [decidable_pred e] : ⁅e | oa⁆ = ∑' x, ite (x ∈ e) (⁅oa⁆ x) 0 :=
trans (prob_event_eq_tsum_indicator oa e) (tsum_congr $ λ _, by { rw set.indicator, congr} )

lemma prob_event_eq_sum_ite [fintype α] [decidable_pred e] :
  ⁅e | oa⁆ = ∑ x, ite (x ∈ e) (⁅oa⁆ x) 0 :=
trans (prob_event_eq_sum_indicator oa e) (finset.sum_congr rfl $
  λ _ _, by {rw set.indicator, congr})

lemma prob_event_eq_sum_fin_support_ite [decidable_pred e] [oa.decidable] :
  ⁅e | oa⁆ = ∑ x in oa.fin_support, ite (x ∈ e) (⁅oa⁆ x) 0 :=
trans (prob_event_eq_sum_fin_support_indicator oa e) (finset.sum_congr rfl $
  λ _ _, by {rw set.indicator, congr})

lemma prob_event_coe_finset_eq_sum (e : finset α) : ⁅↑e | oa⁆ = ∑ x in e, ⁅oa⁆ x :=
by rw [prob_event_eq_tsum_indicator, finset.sum_eq_tsum_indicator]

end sums

section order

variables (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) (e e' : set α)

lemma prob_event_le_one : ⁅e | oa⁆ ≤ 1 :=
(⁅oa⁆.to_outer_measure.mono (set.subset_univ e)).trans
  (le_of_eq $ (⁅oa⁆.to_outer_measure_apply_eq_one_iff _).2 (set.subset_univ ⁅oa⁆.support))

/-- If the intersection of a set `e'` contains all elements of `e` that have non-zero
probability under `⁅oa⁆` then the probability of `e'` is at least as big as that of `e`. -/
lemma prob_event_mono {e e'} (h : (e ∩ oa.support) ⊆ e') : ⁅e | oa⁆ ≤ ⁅e' | oa⁆ :=
pmf.to_outer_measure_mono ⁅oa⁆ (by simpa only [support_eval_dist])

lemma prob_event_mono' {e e'} (h : e ⊆ e') : ⁅e | oa⁆ ≤ ⁅e' | oa⁆ :=
prob_event_mono oa (trans (set.inter_subset_left _ _) h)

lemma prob_event_le_of_eval_dist_apply_le {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : ∀ x ∈ oa.support, ⁅oa⁆ x ≤ ⁅oa'⁆ x) (e : set α) : ⁅e | oa⁆ ≤ ⁅e | oa'⁆ :=
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
lemma prob_event_eq_of_eval_dist_apply_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : ∀ x ∈ oa.support ∪ oa'.support, ⁅oa⁆ x = ⁅oa'⁆ x) (e : set α) : ⁅e | oa⁆ = ⁅e | oa'⁆ :=
antisymm (prob_event_le_of_eval_dist_apply_le (λ x hx, le_of_eq (h x $ or.inl hx)) e)
  (prob_event_le_of_eval_dist_apply_le (λ x hx, le_of_eq (h x $ or.inr hx).symm) e)

lemma prob_event_eq_of_eval_dist_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : ⁅oa⁆ = ⁅oa'⁆) (e : set α) : ⁅e | oa⁆ = ⁅e | oa'⁆ :=
prob_event_eq_of_eval_dist_apply_eq (λ x _, by rw [h]) e

end order

section return

variables (a : α) (e : set α)

@[simp] lemma prob_event_return [decidable_pred e] :
  ⁅e | (return a : oracle_comp spec α)⁆ = ite (a ∈ e) 1 0 :=
by { simp only [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply], congr }

lemma prob_event_return_eq_indicator :
  ⁅e | (return a : oracle_comp spec α)⁆ = e.indicator (λ _, 1) a := 
by rw [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply, set.indicator]

lemma prob_event_pure' [decidable_pred e] :
  ⁅e | (pure' α a : oracle_comp spec α)⁆ = ite (a ∈ e) 1 0 :=
by { simp only [pure'_eq_return, prob_event.def, eval_dist_return,
  pmf.to_outer_measure_pure_apply], congr }

lemma prob_event_pure'_eq_indicator [decidable_pred e] : ⁅e | (pure' α a : oracle_comp spec α)⁆ =
  e.indicator (λ _, 1) a := by simp only [pure'_eq_return, prob_event_return, set.indicator_apply]

lemma prob_event_pure [decidable_pred e] : ⁅e | (pure a : oracle_comp spec α)⁆ = ite (a ∈ e) 1 0 :=
by { simp only [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply], congr }

lemma prob_event_pure_eq_indicator [decidable_pred e] : ⁅e | (pure a : oracle_comp spec α)⁆ =
  e.indicator (λ _, 1) a := by simp only [prob_event_return, set.indicator_apply]

@[simp] lemma prob_event_return_eq_one_iff : ⁅e | (return a : oracle_comp spec α)⁆ = 1 ↔ a ∈ e :=
by rw [prob_event.def, eval_dist_return, pmf.to_outer_measure_apply_eq_one_iff,
  pmf.support_pure, set.singleton_subset_iff]

@[simp] lemma prob_event_return_eq_zero_iff : ⁅e | (return a : oracle_comp spec α)⁆ = 0 ↔ a ∉ e :=
by rw [prob_event.def, eval_dist_return, pmf.to_outer_measure_apply_eq_zero_iff,
  pmf.support_pure, set.disjoint_singleton_left]

end return

section bind

variables (a : α) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (f : α → β) (e : set α) (e' : set β)

@[simp] lemma prob_event_bind_eq_tsum : ⁅e' | oa >>= ob⁆ = ∑' x, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
by simp only [prob_event.def, eval_dist_bind, pmf.to_outer_measure_bind_apply]

lemma prob_event_bind_eq_sum [fintype α] : ⁅e' | oa >>= ob⁆ = ∑ x, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
by simpa only [prob_event_bind_eq_tsum] using tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim)

lemma prob_event_bind_eq_sum_fin_support [oa.decidable] :
  ⁅e' | oa >>= ob⁆ = ∑ x in oa.fin_support, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
(prob_event_bind_eq_tsum oa ob e').trans (tsum_eq_sum (λ x hx,
  by rw [eval_dist_eq_zero_of_not_mem_fin_support hx, zero_mul]))

@[simp] lemma prob_event_bind'_eq_tsum : ⁅e' | bind' α β oa ob⁆ = ∑' x, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
prob_event_bind_eq_tsum oa ob e'

lemma prob_event_bind'_eq_sum [fintype α] : ⁅e' | bind' α β oa ob⁆ = ∑ x, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
prob_event_bind_eq_sum oa ob e'

lemma prob_event_bind'_eq_sum_fin_support [oa.decidable] :
  ⁅e' | bind' α β oa ob⁆ = ∑ x in oa.fin_support, ⁅oa⁆ x * ⁅e' | ob x⁆ :=
prob_event_bind_eq_sum_fin_support oa ob e'

@[simp] lemma prob_event_return_bind : ⁅e' | return a >>= ob⁆ = ⁅e' | ob a⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_return_bind a ob) e'

@[simp] lemma prob_event_bind_return : ⁅e' | oa >>= λ a, return (f a)⁆ = ⁅f ⁻¹' e' | oa⁆ :=
show ⁅e' | f <$> oa⁆ = ⁅f ⁻¹' e' | oa⁆,
by simp only [prob_event.def, eval_dist_map, pmf.to_outer_measure_map_apply]

@[simp] lemma prob_event_bind_return_id : ⁅e | oa >>= return⁆ = ⁅e | oa⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_bind_return_id oa) e

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (oa : spec.range i → oracle_comp spec α) (e : set (spec.range i)) (e' : set α)

@[simp] lemma prob_event_query [decidable_pred e] :
  ⁅e | query i t⁆ = fintype.card e / fintype.card (spec.range i) :=
by simp only [prob_event.def, eval_dist_query, pmf.to_outer_measure_uniform_of_fintype_apply,
  fintype.card_of_finset, finset.filter_congr_decidable]

lemma prob_event_query_bind_eq_tsum :
  ⁅e' | query i t >>= oa⁆ = (∑' x, ⁅e' | oa x⁆) / fintype.card (spec.range i) :=
by simp only [prob_event_bind_eq_tsum, eval_dist_query_apply, div_eq_mul_inv,
  ← ennreal.tsum_mul_left, one_mul, mul_comm]

lemma prob_event_query_bind_eq_sum :
  ⁅e' | query i t >>= oa⁆ = (∑ x, ⁅e' | oa x⁆) / fintype.card (spec.range i) :=
by simp only [prob_event_bind_eq_sum, eval_dist_query_apply, div_eq_mul_inv,
  finset.mul_sum, one_mul, mul_comm]

end query

section map

variables (a : α) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (f : α → β) (g : β → γ) (e : set β) (e' : set γ)

@[simp] lemma prob_event_map : ⁅e | f <$> oa⁆ = ⁅f ⁻¹' e | oa⁆ :=
by simp only [prob_event.def, eval_dist_map, pmf.to_outer_measure_map_apply]

lemma prob_event_map_return : ⁅e | f <$> (return a : oracle_comp spec α)⁆ =
  ⁅e | (return (f a) : oracle_comp spec β)⁆ :=
prob_event_eq_of_eval_dist_eq (by rw [eval_dist_map_return, eval_dist_return]) e

end map

section support

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (e e' : set α)

/-- If two sets have the same intersection with the support of a computation,
then they both have the same probability under `prob_event` -/
lemma prob_event_eq_prob_event_of_inter_support_eq {e e'}
  (h : e ∩ oa.support = e' ∩ oa.support) : ⁅e | oa⁆ = ⁅e' | oa⁆ :=
pmf.to_outer_measure_apply_eq_of_inter_support_eq ⁅oa⁆ (by simpa only [support_eval_dist])

/-- Probability can be calculated on only the intersection of the set with the support. -/
lemma prob_event_eq_prob_event_inter_support : ⁅e | oa⁆ = ⁅e ∩ oa.support | oa⁆ :=
prob_event_eq_prob_event_of_inter_support_eq oa (by rw [set.inter_assoc, set.inter_self])

/-- Given a `finset` containing the `support` of some `oracle_comp`,
  it suffices to take `finset.sum` over that instead of a `tsum` -/
theorem prob_event_eq_sum_of_support_subset [decidable_pred e] (s : finset α) (hs : oa.support ⊆ s) :
  ⁅e | oa⁆ = ∑ x in s, ite (x ∈ e) (⁅oa⁆ x) 0 :=
trans (prob_event_eq_tsum_ite oa e) (tsum_eq_sum (λ x hx,
  by rw [eval_dist_eq_zero_of_not_mem_support (λ hx', hx $ finset.mem_coe.1 (hs hx')), if_t_t]))

theorem prob_event_bind_eq_sum_of_support_subset (e : set β) (s : finset α) (hs : oa.support ⊆ s) :
  ⁅e | oa >>= ob⁆ = ∑ x in s, ⁅oa⁆ x * ⁅e | ob x⁆ :=
trans (prob_event_bind_eq_tsum oa ob e) (tsum_eq_sum (λ x hx,
  by rw [eval_dist_eq_zero_of_not_mem_support (λ h, hx (hs h)), zero_mul]))

@[simp] lemma prob_event_eq_zero_iff_disjoint_support : ⁅e | oa⁆ = 0 ↔ disjoint oa.support e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_zero_iff, support_eval_dist]

@[simp] lemma prob_event_eq_one_iff_support_subset : ⁅e | oa⁆ = 1 ↔ oa.support ⊆ e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_one_iff, support_eval_dist]

end support

section fin_support

variables (oa : oracle_comp spec α) [decidable oa]
  (ob : α → oracle_comp spec β) (e e' : set α)

lemma prob_event_eq_sum_fin_support [decidable_pred e] :
  ⁅e | oa⁆ = ∑ x in oa.fin_support, ite (x ∈ e) (⁅oa⁆ x) 0 :=
(prob_event_eq_sum_of_support_subset _ e oa.fin_support $ support_subset_coe_fin_support oa)

end fin_support

section sets

variables (oa : oracle_comp spec α) (e : set α)

lemma prob_event_eq_eval_dist {x} (hx : x ∈ e)
  (h : ∀ y ≠ x, y ∈ e → y ∉ oa.support) : ⁅e | oa⁆ = ⁅oa⁆ x :=
begin
  refine (prob_event_eq_tsum_indicator oa e).trans (trans (tsum_eq_single x $ λ y hy, _) _),
  { simpa only [set.indicator_apply_eq_zero, eval_dist_eq_zero_iff_not_mem_support] using h y hy },
  { simp only [set.indicator_apply_eq_self, hx, not_true, false_implies_iff] }
end

lemma prob_event_Union_eq_of_pairwise_disjoint (es : ℕ → set α) (h : pairwise (disjoint on es)) :
  ⁅⋃ i, es i | oa⁆ = ∑' i, ⁅es i | oa⁆ :=
by simp only [prob_event.def, pmf.to_outer_measure_apply_Union ⁅oa⁆ h]

lemma prob_event_union_eq_of_disjoint {e e' : set α}
  (h : disjoint e e') : ⁅e ∪ e' | oa⁆ = ⁅e | oa⁆ + ⁅e' | oa⁆ :=
by simpa only [prob_event_eq_to_measure_apply] using
  @measure_theory.measure_union α ⊤ _ e e' h measurable_space.measurable_set_top

lemma prob_event_eq_prob_event_inter_add_prob_event_diff {e s : set α} :
  ⁅e | oa⁆ = ⁅e ∩ s | oa⁆ + ⁅e \ s | oa⁆ :=
trans (by rw [set.inter_union_diff]) (prob_event_union_eq_of_disjoint oa $
  set.disjoint_of_subset_left (set.inter_subset_right _ _) (set.disjoint_diff))

end sets

end distribution_semantics