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

variables {α β γ : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec α)

/-- Probability of a predicate `p` holding after running a computation `oa`.
Defined in terms of the outer measure associated to the corresponding `pmf` by `eval_dist`.
See `prob_event_eq_tsum` for an expression in terms of sums. -/
noncomputable def prob_event (oa : oracle_comp spec α) (p : α → Prop) : ℝ≥0∞ :=
⁅oa⁆.to_outer_measure (p : set α)

notation `⁅` p `|` oa `⁆` := prob_event oa p

lemma prob_event.def' : prob_event oa = ⁅oa⁆.to_outer_measure := rfl

lemma prob_event.def (p : α → Prop) : ⁅p | oa⁆ = ⁅oa⁆.to_outer_measure p := rfl

lemma prob_event_eq_to_measure_apply (p : α → Prop) : ⁅p | oa⁆ = (@pmf.to_measure α ⊤ ⁅oa⁆ p) :=
(@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ ⁅oa⁆ p
  measurable_space.measurable_set_top).symm

@[simp] lemma prob_event_coe_sort (p : α → bool) : ⁅λ x, p x | oa⁆ = ⁅λ x, p x = tt | oa⁆ :=
by simp_rw [eq_self_iff_true]

@[simp] lemma prob_event_set (e : set α) : ⁅e | oa⁆ = ⁅(∈ e) | oa⁆ := rfl

@[simp] lemma prob_event_le_one (p : α → Prop) : ⁅p | oa⁆ ≤ 1 :=
(⁅oa⁆.to_outer_measure.mono (set.subset_univ p)).trans
  (le_of_eq $ (⁅oa⁆.to_outer_measure_apply_eq_one_iff _).2 (set.subset_univ ⁅oa⁆.support))

section basic

variables {p p' : α → Prop}

/-- If the a set `e'` contains all elements of `e` that have non-zero
probability under `⁅oa⁆` then the probability of `e'` is at least as big as that of `e`. -/
lemma prob_event_mono' (h : ∀ x ∈ oa.support, p x → p' x) : ⁅p | oa⁆ ≤ ⁅p' | oa⁆ :=
pmf.to_outer_measure_mono ⁅oa⁆ (λ x hx, h x (mem_support_of_mem_support_eval_dist hx.2) hx.1)

/-- Weaker version of `prob_event_mono` when the subset holds without intersection `support`. -/
lemma prob_event_mono (h : ∀ x, p x → p' x) : ⁅p | oa⁆ ≤ ⁅p' | oa⁆ :=
prob_event_mono' oa (λ x _, h x)

/-- If two propositions are equivalent on the support of a computation,
then the both have the same probability of holding on the result of the computation. -/
lemma prob_event_ext' (h : ∀ x ∈ oa.support, p x ↔ p' x) : ⁅p | oa⁆ = ⁅p' | oa⁆ :=
le_antisymm (prob_event_mono' oa (λ x hx, (h x hx).1)) (prob_event_mono' oa (λ x hx, (h x hx).2))

/-- Weaker version of `prob_event_ext'` when equivalence holds outside the `support`. -/
lemma prob_event_ext {p p' : α → Prop} (h : ∀ x, p x ↔ p' x) : ⁅p | oa⁆ = ⁅p' | oa⁆ :=
congr_arg (λ q, ⁅q | oa⁆) (funext (λ x, propext (h x)))

/-- The probability of the `(= x)` event is just the `prob_output` of that element. -/
@[simp] lemma prob_event_eq_eq_prob_output' (x : α) : ⁅(= x) | oa⁆ = ⁅= x | oa⁆ :=
pmf.to_outer_measure_apply_singleton ⁅oa⁆ x

/-- The probaility of the `(=) x` event is just the `prob_output` of that element. -/
@[simp] lemma prob_event_eq_eq_prob_output (x : α) : ⁅(=) x | oa⁆ = ⁅= x | oa⁆ :=
trans (prob_event_ext oa (λ _, eq_comm)) (prob_event_eq_eq_prob_output' oa x)

lemma prob_event_eq_of_eval_dist_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : ⁅oa⁆ = ⁅oa'⁆) (p : α → Prop) : ⁅p | oa⁆ = ⁅p | oa'⁆ :=
by simp only [h, prob_event.def]

end basic

section sums

variable (p : α → Prop)

/-- The probability of an event `p` as a sum over the output type, using `set.indicator`
to filter out elements that don't satisfy `p x`. -/
lemma prob_event_eq_tsum_indicator :
  ⁅p | oa⁆ = ∑' x : α, {x ∈ oa.support | p x}.indicator ⁅oa⁆ x :=
begin
  refine trans (⁅oa⁆.to_outer_measure_apply p) (tsum_congr (λ x, _)),
  by_cases hx : x ∈ oa.support ∧ p x,
  { exact trans (set.indicator_of_mem hx.2 ⁅oa⁆) (symm $ set.indicator_of_mem hx ⁅oa⁆) },
  { refine or.rec_on (not_and_distrib.1 hx) (λ hx, _) (λ hx, _),
    { exact trans (set.indicator_apply_eq_zero.2 (λ _, prob_output_eq_zero hx))
        (symm $ set.indicator_apply_eq_zero.2 (λ _, prob_output_eq_zero hx)) },
    { exact trans (set.indicator_of_not_mem hx ⁅oa⁆)
        (symm $ set.indicator_of_not_mem (λ h, hx h.2) ⁅oa⁆) } }
end

/-- Weaker version of `prob_event_eq_tsum_indicator` that doesn't explicitly restrict the
set of elements to the support of the computation (implicitly the probabilities are still zero). -/
lemma prob_event_eq_tsum_indicator' : ⁅p | oa⁆ = ∑' x : α, {x | p x}.indicator ⁅oa⁆ x :=
⁅oa⁆.to_outer_measure_apply p

lemma prob_event_mem_set_eq_tsum_indicator (e : set α) :
  ⁅(∈ e) | oa⁆ = ∑' x, e.indicator ⁅oa⁆ x :=
by rw [prob_event_eq_tsum_indicator', set.set_of_mem_eq]

/-- If we have `decidable_eq` on the output type of a computation,
we can write the probability of an event as a finite sum over the `fin_support` of the computation,
using `set.indicator` to filter elements not in the event. -/
lemma prob_event_eq_sum_indicator [decidable_eq α] :
  ⁅p | oa⁆ = ∑ x in oa.fin_support, {x | p x}.indicator ⁅oa⁆ x :=
trans (prob_event_eq_tsum_indicator' oa p) (tsum_eq_sum (λ x hx,
  set.indicator_apply_eq_zero.2 (λ h, prob_output_eq_zero' hx)))

/-- The probability of an event `p` as a sum over all outputs `x` of `oa` that satisfy `p`,
using a `subtype` in the domain to restrict the included probabilities. -/
lemma prob_event_eq_tsum_subtype : ⁅p | oa⁆ = ∑' x : {x ∈ oa.support| p x}, ⁅= x | oa⁆ :=
by rw [prob_event_eq_tsum_indicator, tsum_subtype, prob_output.def']

/-- Version of `prob_event_eq_tsum_subtype` that doesn't explicitly restrict the set of elements
to the support of the computation (implicitly the probabilities are still zero). -/
lemma prob_event_eq_tsum_subtype' : ⁅p | oa⁆ = ∑' x : {x | p x}, ⁅= x | oa⁆ :=
by rw [prob_event_eq_tsum_indicator', tsum_subtype, prob_output.def']

/-- If `p` is decidable, then we can write the probability of an event as a `tsum` over the
entire output type, using an `ite` statement to exclude outputs not satisfying `p`. -/
@[simp] lemma prob_event_eq_tsum_ite [decidable_pred p] :
  ⁅p | oa⁆ = ∑' x : α, if p x then ⁅= x | oa⁆ else 0 :=
trans (⁅oa⁆.to_outer_measure_apply p) (by simp_rw [set.indicator, set.mem_def, prob_output.def])

/-- If we have `decidable_eq` on the output type and `decidable_pred` of the event,
we can write the probability of an event as a finite sum over the `fin_support` of the computation,
using an if-then-else statement to filter elements not in the event. -/
lemma prob_event_eq_sum_ite [decidable_eq α] [decidable_pred p] :
  ⁅p | oa⁆ = ∑ x in oa.fin_support, if p x then ⁅= x | oa⁆ else 0 :=
trans (prob_event_eq_tsum_ite oa p) (tsum_eq_sum (λ x hx,
  ite_eq_right_iff.2 (λ _, prob_output_eq_zero' hx)))

/-- If we have `decidable_eq` on the output type and `decidable_pred` of the event,
we can write the probability of an event as a finite sum over the `fin_support` of the computation,
by filtering the computation's `fin_support` by the predicate. -/
@[simp] lemma prob_event_eq_sum_filter [decidable_eq α] [decidable_pred p] :
  ⁅p | oa⁆ = ∑ x in oa.fin_support.filter p, ⁅= x | oa⁆ :=
trans (prob_event_eq_tsum_ite oa p) (trans (tsum_eq_sum (λ x hx, ite_eq_right_iff.2 (λ hpx,
  prob_output_eq_zero' (λ h, hx (finset.mem_filter.2 ⟨h, hpx⟩)))))
    (finset.sum_congr rfl (λ x hx, if_pos (finset.mem_filter.1 hx).2)))

/-- The probability of an output belonging to a `finset` can be written as the sum
of the probabilities of getting each element of the set from the computation. -/
@[simp] lemma prob_event_mem_finset_eq_sum (s : finset α) :
  ⁅(∈ s) | oa⁆ = ∑ x in s, ⁅= x | oa⁆ :=
trans (prob_event_eq_tsum_indicator' oa (∈ s)) (trans (tsum_eq_sum ((λ x hx,
  set.indicator_of_not_mem hx _))) (finset.sum_congr rfl (λ x hx, set.indicator_of_mem hx ⁅oa⁆)))

end sums

section sets

/-- The probability of a singleton set is just the `prob_output` of that element. -/
lemma prob_event_mem_singleton_eq_prob_output (x : α) : ⁅(∈ ({x} : set α)) | oa⁆ = ⁅= x | oa⁆ :=
by simp only [set.mem_singleton_iff, prob_event_eq_eq_prob_output']

end sets

-- lemma prob_event_ext (h : ∀ x ∈ oa.support, x ∈ e ↔ x ∈ e') : ⁅e | oa⁆ = ⁅e' | oa⁆ :=
-- begin
--   rw [prob_event_eq_tsum_indicator, prob_event_eq_tsum_indicator],
--   refine tsum_congr (λ x, _),
--   by_cases hx : x ∈ oa.support,
--   { by_cases hx' : x ∈ e,
--     { simp only [hx', (h x hx).1 hx', set.indicator_of_mem, eval_dist_apply_eq_prob_output] },
--     { simp only [hx', mt ((h x hx).2) hx', set.indicator_of_not_mem, not_false_iff] } },
--   { rw [set.indicator_apply_eq_zero.2 (λ _, eval_dist_apply_eq_zero hx),
--       set.indicator_apply_eq_zero.2 (λ _, eval_dist_apply_eq_zero hx)] }
-- end

-- lemma prob_event_ext' (h : ∀ x ∈ oa.support, p x ↔ p' x) : ⁅p | oa⁆ = ⁅p' | oa⁆ :=
-- prob_event_ext oa p p' h

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

end oracle_comp