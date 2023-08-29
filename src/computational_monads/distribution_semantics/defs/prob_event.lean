/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.prob_output

/-!
# Probability of Events

This file defines the probability of some event holding after running a computation.
The definition is in terms of the `measure` associated to the `pmf` given by `eval_dist`.
We also introduce the notation `⁅e | oa⁆` for the probability of the output of `oa` being in `e`.
It also allows for writing `⁅λ x, p x | oa⁆` for the probability of `p` holding on the output.

This definition is equivalent to one in terms of summations, in particular an infinite `tsum`.
If the support or event is a `finset`, we can also write it in terms of `finset.sum`.
In the extreme cases of the probability being `0` or `1`, we can also work purely in terms
of `support`, with it being either disjoint from or a subset of the event respectively.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec} (oa : oracle_comp spec α) (e e' : set α)

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

lemma prob_event_le_one : ⁅e | oa⁆ ≤ 1 :=
(⁅oa⁆.to_outer_measure.mono (set.subset_univ e)).trans
  (le_of_eq $ (⁅oa⁆.to_outer_measure_apply_eq_one_iff _).2 (set.subset_univ ⁅oa⁆.support))

lemma prob_event_eq_of_iff (h : ∀ x, e x ↔ e' x) : ⁅e | oa⁆ = ⁅e' | oa⁆ :=
congr_arg (λ e, ⁅e | oa⁆) (set.ext h)

lemma prob_event_eq_of_mem_iff (h : ∀ x, x ∈ e ↔ x ∈ e') : ⁅e | oa⁆ = ⁅e' | oa⁆ :=
congr_arg (λ e, ⁅e | oa⁆) (set.ext h)

/-- If the a set `e'` contains all elements of `e` that have non-zero
probability under `⁅oa⁆` then the probability of `e'` is at least as big as that of `e`. -/
lemma prob_event_mono {e e'} (h : (e ∩ oa.support) ⊆ e') : ⁅e | oa⁆ ≤ ⁅e' | oa⁆ :=
pmf.to_outer_measure_mono ⁅oa⁆ (by simpa only [support_eval_dist])

/-- Weaker version of `prob_event_mono` when the subset holds without intersection `support`. -/
lemma prob_event_mono' {e e'} (h : e ⊆ e') : ⁅e | oa⁆ ≤ ⁅e' | oa⁆ :=
prob_event_mono oa (trans (set.inter_subset_left _ _) h)

/-- The probability of a singleton set happening is just the `eval_dist` of that element. -/
@[simp] lemma prob_event_singleton_eq_prob_output (x : α) : ⁅{x} | oa⁆ = ⁅= x | oa⁆ :=
by rw [prob_event.def, pmf.to_outer_measure_apply_singleton, prob_output]

/-- The probaility of the `(=) x` event is just the `eval_dist` of that element. -/
@[simp] lemma prob_event_eq_eq_prob_output (x : α) : ⁅(=) x | oa⁆ = ⁅= x | oa⁆ :=
trans (congr_arg _ (set.ext $ λ y, eq_comm)) (prob_event_singleton_eq_prob_output oa x)

lemma prob_event_eq_of_eval_dist_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : ⁅oa⁆ = ⁅oa'⁆) (e : set α) : ⁅e | oa⁆ = ⁅e | oa'⁆ :=
by simp only [h, prob_event.def]

section sums

/-- Probability of an event in terms of non-decidable `set.indicator` sum -/
lemma prob_event_eq_tsum_indicator : ⁅e | oa⁆ = ∑' x, e.indicator ⁅oa⁆ x :=
pmf.to_outer_measure_apply ⁅oa⁆ e

lemma prob_event_eq_sum_indicator [fintype α] : ⁅e | oa⁆ = ∑ x, e.indicator ⁅oa⁆ x :=
(prob_event_eq_tsum_indicator oa e).trans (tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim))

lemma prob_event_eq_sum_fin_support_indicator :
  ⁅e | oa⁆ = ∑ x in oa.fin_support, e.indicator ⁅oa⁆ x :=
(prob_event_eq_tsum_indicator oa e).trans (tsum_eq_sum $
  λ a ha, set.indicator_apply_eq_zero.2 (λ _, prob_output_eq_zero' ha))

/-- Probability of an event in terms of a decidable `ite` sum-/
lemma prob_event_eq_tsum_ite [decidable_pred e] : ⁅e | oa⁆ = ∑' x, ite (x ∈ e) ⁅= x | oa⁆ 0 :=
trans (prob_event_eq_tsum_indicator oa e) (tsum_congr $ λ _, by { rw set.indicator, congr} )

lemma prob_event_eq_sum_ite [fintype α] [decidable_pred e] :
  ⁅e | oa⁆ = ∑ x, ite (x ∈ e) (⁅oa⁆ x) 0 :=
trans (prob_event_eq_sum_indicator oa e) (finset.sum_congr rfl $
  λ _ _, by {rw set.indicator, congr})

lemma prob_event_eq_sum_fin_support_ite [decidable_pred e] :
  ⁅e | oa⁆ = ∑ x in oa.fin_support, ite (x ∈ e) (⁅oa⁆ x) 0 :=
trans (prob_event_eq_sum_fin_support_indicator oa e) (finset.sum_congr rfl $
  λ _ _, by {rw set.indicator, congr})

/-- If the event is a finite set, then the probability can be written as a sum over itself. -/
lemma prob_event_coe_finset_eq_sum (e : finset α) : ⁅↑e | oa⁆ = ∑ x in e, ⁅oa⁆ x :=
by rw [prob_event_eq_tsum_indicator, sum_eq_tsum_indicator]

end sums

section support

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
lemma prob_event_eq_sum_of_support_subset [decidable_pred e] (s : finset α)
  (hs : oa.support ⊆ s) : ⁅e | oa⁆ = ∑ x in s, ite (x ∈ e) (⁅= x | oa⁆) 0 :=
trans (prob_event_eq_tsum_ite oa e) (tsum_eq_sum (λ x hx,
  by rw [prob_output_eq_zero (λ hx', hx $ finset.mem_coe.1 (hs hx')), if_t_t]))

@[simp] lemma prob_event_eq_zero_iff_disjoint_support : ⁅e | oa⁆ = 0 ↔ disjoint oa.support e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_zero_iff, support_eval_dist]

lemma prob_event_eq_zero_of_dijoint_support (h : disjoint oa.support e) : ⁅e | oa⁆ = 0 :=
(oa.prob_event_eq_zero_iff_disjoint_support e).2 h

@[simp] lemma prob_event_eq_one_iff_support_subset : ⁅e | oa⁆ = 1 ↔ oa.support ⊆ e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_one_iff, support_eval_dist]

lemma prob_event_eq_one_of_support_subset (h : oa.support ⊆ e) : ⁅e | oa⁆ = 1 :=
(oa.prob_event_eq_one_iff_support_subset e).2 h

end support

section sets

-- TODO: Prop versions for everything

lemma prob_event_empty (oa : oracle_comp spec α) : ⁅∅ | oa⁆ = 0 :=
⁅oa⁆.to_outer_measure.empty

@[simp] lemma prob_event_insert (x : α) : ⁅insert x e | oa⁆ = ⁅= x | oa⁆ + ⁅e \ {x} | oa⁆ :=
⁅oa⁆.to_outer_measure_apply_insert x e

lemma prob_event_compl : ⁅eᶜ | oa⁆ = 1 - ⁅e | oa⁆ :=
⁅oa⁆.to_outer_measure_apply_compl e

lemma prob_event_not (p : α → Prop) : ⁅λ x, ¬ p x | oa⁆ = 1 - ⁅p | oa⁆ :=
prob_event_compl oa p

lemma prob_event_diff : ⁅e \ e' | oa⁆ = ⁅e | oa⁆ - ⁅e ∩ e' | oa⁆ :=
⁅oa⁆.to_outer_measure_apply_diff e e'

lemma prob_event_inter_add_diff {e e'} : ⁅e ∩ e' | oa⁆ + ⁅e \ e' | oa⁆ = ⁅e | oa⁆ :=
⁅oa⁆.to_outer_measure_apply_inter_add_diff e e'

lemma prob_event_union_le_add (oa : oracle_comp spec α) (e e' : set α) :
  ⁅e ∪ e' | oa⁆ ≤ ⁅e | oa⁆ + ⁅e' | oa⁆ :=
⁅oa⁆.to_outer_measure.union e e'

lemma prob_event_Union_le_tsum (oa : oracle_comp spec α) (e : ℕ → set α) :
  ⁅⋃ n, e n | oa⁆ ≤ ∑' n, ⁅e n | oa⁆ :=
⁅oa⁆.to_outer_measure.Union e

lemma prob_event_Union_eq_of_pairwise_disjoint (es : ℕ → set α) (h : pairwise (disjoint on es)) :
  ⁅⋃ i, es i | oa⁆ = ∑' i, ⁅es i | oa⁆ :=
⁅oa⁆.to_outer_measure_apply_Union h

lemma prob_event_union_eq_of_disjoint {e e' : set α}
  (h : disjoint e e') : ⁅e ∪ e' | oa⁆ = ⁅e | oa⁆ + ⁅e' | oa⁆ :=
⁅oa⁆.to_outer_measure_apply_union h

end sets

lemma prob_event_eq_prob_output (x : α) {e : set α} (hx : x ∈ e)
  (h : ∀ y ≠ x, y ∈ e → y ∉ oa.support) : ⁅e | oa⁆ = ⁅= x | oa⁆ :=
begin
  refine (prob_event_eq_tsum_indicator oa e).trans (trans (tsum_eq_single x $ λ y hy, _) _),
  { simpa [set.indicator_apply_eq_zero, prob_output_eq_zero_iff] using h y hy },
  { simp [set.indicator_apply_eq_self, hx, not_true, false_implies_iff] }
end

/-- If the all elements in `oa.support` have higher probability under -/
lemma prob_event_le_of_prob_output_le {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
   {e : set α} (h : ∀ x ∈ e ∩ oa.support, ⁅= x | oa⁆ ≤ ⁅= x | oa'⁆) : ⁅e | oa⁆ ≤ ⁅e | oa'⁆ :=
begin
  simp only [prob_event_eq_tsum_indicator],
  refine ennreal.tsum_le_tsum (λ x, _),
  refine set.indicator_apply_le (λ hxe, _),
  by_cases hx : x ∈ oa.support,
  { rw [(set.indicator_apply_eq_self.2 $ λ hxe', (hxe' hxe).elim)],
    exact h x ⟨hxe, hx⟩ },
  { simp only [eval_dist_apply_eq_prob_output, prob_output_eq_zero hx, zero_le'] }
end

/-- If the `eval_dist` agrees on all elements of the support, then `prob_event` agrees as well. -/
lemma prob_event_eq_of_prob_output_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  {e : set α} (h : ∀ x ∈ e ∩ (oa.support ∪ oa'.support), ⁅= x | oa⁆ = ⁅= x | oa'⁆) :
  ⁅e | oa⁆ = ⁅e | oa'⁆ :=
begin
  simp only [prob_event_eq_tsum_indicator],
  refine tsum_congr (λ x, _),
  simp only [set.indicator],
  split_ifs with hx,
  { by_cases hx' : x ∈ (oa.support ∪ oa'.support),
    { exact h x ⟨hx, hx'⟩ },
    { rw [set.mem_union, not_or_distrib] at hx',
      simp [prob_output_eq_zero hx'.1, prob_output_eq_zero hx'.2] } },
  { refl }
end

@[simp] lemma prob_event_coe_sort (p : α → bool) : ⁅λ x, p x | oa⁆ = ⁅λ x, p x = tt | oa⁆ :=
by simp_rw [eq_self_iff_true]

end oracle_comp