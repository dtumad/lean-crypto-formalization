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

/-- Probability of a predicate `p` holding after running a computation `oa`.
Defined in terms of the outer measure associated to the corresponding `pmf` by `eval_dist`.
See `prob_event_eq_tsum` for an expression in terms of sums.
While a set `e : set α` can be used directly as the argument `p`,
it's generally better to use `(∈ e)` as this aligns better with existing lemmas. -/
noncomputable def prob_event (oa : oracle_comp spec α) (p : α → Prop) : ℝ≥0∞ :=
⁅oa⁆.to_outer_measure (p : set α)

notation `⁅` p `|` oa `⁆` := prob_event oa p

lemma prob_event.def' (oa : oracle_comp spec α) : prob_event oa = ⁅oa⁆.to_outer_measure := rfl

lemma prob_event.def (oa : oracle_comp spec α) (p : α → Prop) :
  ⁅p | oa⁆ = ⁅oa⁆.to_outer_measure p := rfl

lemma prob_event_eq_to_measure_apply (oa : oracle_comp spec α) (p : α → Prop) :
  ⁅p | oa⁆ = (@pmf.to_measure α ⊤ ⁅oa⁆ p) :=
(@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ ⁅oa⁆ p
  measurable_space.measurable_set_top).symm

@[simp] lemma prob_event_coe_sort (oa : oracle_comp spec α) (p : α → bool) :
  ⁅λ x, p x | oa⁆ = ⁅λ x, p x = tt | oa⁆ := by simp_rw [eq_self_iff_true]

lemma prob_event_set_eq_prob_event_mem (oa : oracle_comp spec α) (e : set α) :
  ⁅e | oa⁆ = ⁅(∈ e) | oa⁆ := rfl

@[simp] lemma prob_event_le_one {oa : oracle_comp spec α} {p : α → Prop} : ⁅p | oa⁆ ≤ 1 :=
(⁅oa⁆.to_outer_measure.mono (set.subset_univ p)).trans
  (le_of_eq $ (⁅oa⁆.to_outer_measure_apply_eq_one_iff _).2 (set.subset_univ ⁅oa⁆.support))

@[simp] lemma prob_event_lt_one_iff {oa : oracle_comp spec α} {p : α → Prop} :
  ⁅p | oa⁆ < 1 ↔ ∃ x ∈ oa.support, ¬ p x :=
by simp_rw [lt_iff_le_and_ne, prob_event_le_one, true_and, prob_event.def, ne.def,
  pmf.to_outer_measure_apply_eq_one_iff, set.not_subset, support_eval_dist, set.mem_def]

@[simp] lemma prob_event_ne_top {oa : oracle_comp spec α} {p : α → Prop} : ⁅p | oa⁆ ≠ ⊤ :=
ne_top_of_le_ne_top (ennreal.one_ne_top) prob_event_le_one

@[simp] lemma prob_event_lt_top {oa : oracle_comp spec α} {p : α → Prop} : ⁅p | oa⁆ < ⊤ :=
lt_top_iff_ne_top.2 prob_event_ne_top

lemma prob_event_eq_of_eval_dist_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : ⁅oa⁆ = ⁅oa'⁆) (p : α → Prop) : ⁅p | oa⁆ = ⁅p | oa'⁆ :=
by simp only [h, prob_event.def]


lemma prob_event_le_of_prob_output_le {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  {p : α → Prop} (h : ∀ x, p x → ⁅= x | oa⁆ ≤ ⁅= x | oa'⁆) : ⁅p | oa⁆ ≤ ⁅p | oa'⁆ :=
begin
  simp_rw [prob_event.def, pmf.to_outer_measure_apply],
  refine ennreal.tsum_le_tsum (λ x, _),
  by_cases hpx : p x,
  { simp only [set.indicator_of_mem hpx, ← prob_output.def, h x hpx] },
  { simp only [set.indicator_of_not_mem hpx, zero_le'] },
end

lemma prob_event_eq_of_prob_output_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  {p : α → Prop} (h : ∀ x, p x → ⁅= x | oa⁆ = ⁅= x | oa'⁆) : ⁅p | oa⁆ = ⁅p | oa'⁆ :=
le_antisymm (prob_event_le_of_prob_output_le (λ x hx, le_of_eq (h x hx)))
  (prob_event_le_of_prob_output_le (λ x hx, le_of_eq (h x hx).symm))

/-- If the a set `e'` contains all elements of `e` that have non-zero
probability under `⁅oa⁆` then the probability of `e'` is at least as big as that of `e`. -/
lemma prob_event_mono' {oa : oracle_comp spec α} {p p' : α → Prop}
  (h : ∀ x ∈ oa.support, p x → p' x) : ⁅p | oa⁆ ≤ ⁅p' | oa⁆ :=
pmf.to_outer_measure_mono ⁅oa⁆ (λ x hx, h x (mem_support_of_mem_support_eval_dist hx.2) hx.1)

/-- Weaker version of `prob_event_mono` when the subset holds without intersection `support`. -/
lemma prob_event_mono (oa : oracle_comp spec α) {p p' : α → Prop}
  (h : ∀ x, p x → p' x) : ⁅p | oa⁆ ≤ ⁅p' | oa⁆ :=
prob_event_mono' (λ x _, h x)

/-- If two propositions are equivalent on the support of a computation,
then the both have the same probability of holding on the result of the computation. -/
lemma prob_event_ext' {oa : oracle_comp spec α} {p p' : α → Prop}
  (h : ∀ x ∈ oa.support, p x ↔ p' x) : ⁅p | oa⁆ = ⁅p' | oa⁆ :=
le_antisymm (prob_event_mono' (λ x hx, (h x hx).1)) (prob_event_mono' (λ x hx, (h x hx).2))

/-- Weaker version of `prob_event_ext'` when equivalence holds outside the `support`. -/
lemma prob_event_ext (oa : oracle_comp spec α) {p p' : α → Prop}
  (h : ∀ x, p x ↔ p' x) : ⁅p | oa⁆ = ⁅p' | oa⁆ :=
congr_arg (λ q, ⁅q | oa⁆) (funext (λ x, propext (h x)))

/-- The probability of the `(= x)` event is just the `prob_output` of that element. -/
@[simp] lemma prob_event_eq_eq_prob_output' (oa : oracle_comp spec α)
  (x : α) : ⁅(= x) | oa⁆ = ⁅= x | oa⁆ :=
pmf.to_outer_measure_apply_singleton ⁅oa⁆ x

/-- The probaility of the `(=) x` event is just the `prob_output` of that element. -/
@[simp] lemma prob_event_eq_eq_prob_output (oa : oracle_comp spec α)
  (x : α) : ⁅(=) x | oa⁆ = ⁅= x | oa⁆ :=
trans (prob_event_ext oa (λ _, eq_comm)) (prob_event_eq_eq_prob_output' oa x)

section sums

variables (oa : oracle_comp spec α) (p : α → Prop)

section indicator

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

/-- If we have `decidable_eq` on the output type of a computation,
we can write the probability of an event as a finite sum over the `fin_support` of the computation,
using `set.indicator` to filter elements not in the event. -/
lemma prob_event_eq_sum_indicator [decidable_eq α] :
  ⁅p | oa⁆ = ∑ x in oa.fin_support, {x | p x}.indicator ⁅oa⁆ x :=
(prob_event_eq_tsum_indicator' oa p).trans (tsum_eq_sum (λ x hx,
  set.indicator_apply_eq_zero.2 (λ h, prob_output_eq_zero' hx)))

lemma prob_event_eq_sum_fintype_indicator [fintype α] :
  ⁅p | oa⁆ = ∑ x : α, {x | p x}.indicator ⁅oa⁆ x :=
trans (prob_event_eq_tsum_indicator' oa p) (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))

end indicator

section subtype

/-- The probability of an event `p` as a sum over all outputs `x` of `oa` that satisfy `p`,
using a `subtype` in the domain to restrict the included probabilities. -/
lemma prob_event_eq_tsum_subtype : ⁅p | oa⁆ = ∑' x : {x ∈ oa.support| p x}, ⁅= x | oa⁆ :=
by rw [prob_event_eq_tsum_indicator, tsum_subtype, prob_output.def']

/-- Version of `prob_event_eq_tsum_subtype` that doesn't explicitly restrict the set of elements
to the support of the computation (implicitly the probabilities are still zero). -/
lemma prob_event_eq_tsum_subtype' : ⁅p | oa⁆ = ∑' x : {x | p x}, ⁅= x | oa⁆ :=
by rw [prob_event_eq_tsum_indicator', tsum_subtype, prob_output.def']

/-- The probability of a result belonging to a set `e` written as a sum over possible outputs,
using `e.indicator` to filter the elements not belonging to the set. -/
lemma prob_event_mem_set_eq_tsum_subtype (e : set α) : ⁅(∈ e) | oa⁆ = ∑' x : e, ⁅= x | oa⁆ :=
by rw [prob_event_eq_tsum_subtype', set.set_of_mem_eq]

end subtype

section ite

/-- If `p` is decidable, then we can write the probability of an event as a `tsum` over the
entire output type, using an `ite` statement to exclude outputs not satisfying `p`. -/
lemma prob_event_eq_tsum_ite [decidable_pred p] :
  ⁅p | oa⁆ = ∑' x : α, if p x then ⁅= x | oa⁆ else 0 :=
trans (⁅oa⁆.to_outer_measure_apply p) (by simp_rw [set.indicator, set.mem_def, prob_output.def])

/-- If we have `decidable_eq` on the output type and `decidable_pred` of the event,
we can write the probability of an event as a finite sum over the `fin_support` of the computation,
using an if-then-else statement to filter elements not in the event. -/
lemma prob_event_eq_sum_ite [decidable_eq α] [decidable_pred p] :
  ⁅p | oa⁆ = ∑ x in oa.fin_support, if p x then ⁅= x | oa⁆ else 0 :=
(prob_event_eq_tsum_ite oa p).trans (tsum_eq_sum (λ x hx,
  ite_eq_right_iff.2 (λ _, prob_output_eq_zero' hx)))

lemma prob_event_eq_sum_fintype_ite [fintype α] [decidable_pred p] :
  ⁅p | oa⁆ = ∑ x : α, if p x then ⁅= x | oa⁆ else 0 :=
(prob_event_eq_tsum_ite oa p).trans (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))

end ite

section filter

/-- If we have `decidable_eq` on the output type and `decidable_pred` of the event,
we can write the probability of an event as a finite sum over the `fin_support` of the computation,
by filtering the computation's `fin_support` by the predicate. -/
lemma prob_event_eq_sum_filter [decidable_eq α] [decidable_pred p] :
  ⁅p | oa⁆ = ∑ x in oa.fin_support.filter p, ⁅= x | oa⁆ :=
trans (prob_event_eq_tsum_ite oa p) (trans (tsum_eq_sum (λ x hx, ite_eq_right_iff.2 (λ hpx,
  prob_output_eq_zero' (λ h, hx (finset.mem_filter.2 ⟨h, hpx⟩)))))
    (finset.sum_congr rfl (λ x hx, if_pos (finset.mem_filter.1 hx).2)))

/-- Alternative to `prob_event_eq_sum_filter` when we have `fintype α` but not `decidable_eq α`.-/
lemma prob_event_eq_sum_filter_univ [fintype α] [decidable_pred p] :
  ⁅p | oa⁆ = ∑ x in finset.univ.filter p, ⁅= x | oa⁆ :=
by simpa only [prob_event_eq_tsum_ite, finset.sum_filter]  
  using tsum_eq_sum (λ x h, (h (finset.mem_univ x)).elim)

end filter

/-- The probability of an output belonging to a `finset` can be written as the sum
of the probabilities of getting each element of the set from the computation. -/
lemma prob_event_mem_finset_eq_sum (s : finset α) : ⁅(∈ s) | oa⁆ = ∑ x in s, ⁅= x | oa⁆ :=
trans (prob_event_eq_tsum_indicator' oa (∈ s)) (trans (tsum_eq_sum ((λ x hx,
  set.indicator_of_not_mem hx _))) (finset.sum_congr rfl (λ x hx, set.indicator_of_mem hx ⁅oa⁆)))

end sums

section support

variables (oa : oracle_comp spec α)

lemma prob_event_and_mem_support (p : α → Prop) : ⁅λ x, p x ∧ x ∈ oa.support | oa⁆ = ⁅p | oa⁆ :=
prob_event_ext' (λ x hx, and_iff_left hx)

lemma prob_event_mem_support_and (p : α → Prop) : ⁅λ x, x ∈ oa.support ∧ p x | oa⁆ = ⁅p | oa⁆ :=
prob_event_ext' (λ x hx, and_iff_right hx)

@[simp] lemma prob_event_eq_zero_iff (p : α → Prop) : ⁅p | oa⁆ = 0 ↔ ∀ x ∈ oa.support, ¬ p x :=
by simp only [prob_event_eq_tsum_indicator', ennreal.tsum_eq_zero, set.indicator_apply_eq_zero,
  imp_not_comm, set.mem_set_of_eq, eval_dist_apply_eq_prob_output, prob_output_eq_zero_iff] 

lemma prob_event_eq_zero {oa : oracle_comp spec α} {p : α → Prop}
  (h : ∀ x ∈ oa.support, ¬ p x) : ⁅p | oa⁆ = 0 :=
(prob_event_eq_zero_iff oa p).2 h

@[simp] lemma prob_event_eq_one_iff (p : α → Prop) : ⁅p | oa⁆ = 1 ↔ ∀ x ∈ oa.support, p x :=
by simpa only [prob_event.def, pmf.to_outer_measure_apply_eq_one_iff, support_eval_dist]

lemma prob_event_eq_one {oa : oracle_comp spec α} {p : α → Prop}
  (h : ∀ x ∈ oa.support, p x) : ⁅p | oa⁆ = 1 :=
(prob_event_eq_one_iff oa p).2 h

lemma prob_event_eq_prob_output {oa : oracle_comp spec α} {p : α → Prop}
  (x : α) (hpx : p x) (h : ∀ y ∈ oa.support, p y → y = x) : ⁅p | oa⁆ = ⁅= x | oa⁆ :=
begin
  by_cases hx : x ∈ oa.support,
  { have : {x ∈ oa.support | p x} = {x} := subset_antisymm (λ y hy, h y hy.1 hy.2)
      (λ y hy, (set.mem_singleton_iff.1 hy).symm ▸ ⟨hx, hpx⟩),
    rw [prob_event_eq_tsum_subtype, this, tsum_singleton] },
  { have : {x ∈ oa.support | p x} = ∅,
    from set.eq_empty_of_forall_not_mem (λ y hy, hx (h y hy.1 hy.2 ▸ hy.1)),
    rw [prob_event_eq_tsum_subtype, this, tsum_empty, prob_output_eq_zero hx] }
end

end support

section bool

variables (oa : oracle_comp spec α)

@[simp] lemma prob_event_const (p : Prop) [hp : decidable p] :
  ⁅λ _, p | oa⁆ = if p then 1 else 0 :=
by split_ifs with hp; simp only [hp, prob_event_eq_one_iff,
  prob_event_eq_zero_iff, not_false_iff, implies_true_iff]

lemma prob_event_true : ⁅λ _, true | oa⁆ = 1 := by rw [prob_event_const, if_true]

lemma prob_event_false : ⁅λ _, false | oa⁆ = 0 := by rw [prob_event_const, if_false]

@[simp] lemma prob_event_not (p : α → Prop) : ⁅λ x, ¬ p x | oa⁆ = 1 - ⁅p | oa⁆ :=
⁅oa⁆.to_outer_measure_apply_compl p

lemma prob_event_or_add_prob_event_and (p q : α → Prop) :
  ⁅λ x, p x ∨ q x | oa⁆ + ⁅λ x, p x ∧ q x | oa⁆ = ⁅p | oa⁆ + ⁅q | oa⁆ :=
by simpa only [prob_event_eq_to_measure_apply]
  using measure_theory.measure_union_add_inter _ measurable_space.measurable_set_top

lemma prob_event_or_eq_add_sub_prob_event_and (p q : α → Prop) :
  ⁅λ x, p x ∨ q x | oa⁆ = ⁅p | oa⁆ + ⁅q | oa⁆ - ⁅λ x, p x ∧ q x | oa⁆ :=
by simpa only [← prob_event_or_add_prob_event_and oa p q]
  using symm (ennreal.add_sub_cancel_right prob_event_ne_top)

lemma prob_event_and_eq_add_sub_prob_event_or (p q : α → Prop) :
  ⁅λ x, p x ∧ q x | oa⁆ = ⁅p | oa⁆ + ⁅q | oa⁆ - ⁅λ x, p x ∨ q x | oa⁆ :=
by simpa only [← prob_event_or_add_prob_event_and oa p q]
  using symm (ennreal.add_sub_cancel_left prob_event_ne_top)

lemma prob_event_or (p q : α → Prop) :
  ⁅λ x, p x ∨ q x | oa⁆ = ⁅p | oa⁆ + ⁅λ x, ¬ p x ∧ q x | oa⁆ :=
trans (by simp only [or_and_distrib_left, ←and_assoc, or_not, true_and, and_not_self,
  false_and, prob_event_const, if_false, add_zero]) (prob_event_or_add_prob_event_and oa p _)

lemma prob_event_or' (p q : α → Prop) :
  ⁅λ x, p x ∨ q x | oa⁆ = ⁅q | oa⁆ + ⁅λ x, ¬ q x ∧ p x | oa⁆ :=
trans (prob_event_ext oa (λ x, or_comm (p x) (q x))) (prob_event_or oa q p)

lemma prob_event_or_eq_add {p q : α → Prop} (h : ∀ x ∈ oa.support, p x → ¬ q x) :
  ⁅λ x, p x ∨ q x | oa⁆ = ⁅p | oa⁆ + ⁅q | oa⁆ :=
have ⁅λ x, p x ∧ q x | oa⁆ = 0 := by simpa only [prob_event_eq_zero_iff, not_and] using h,
by rw [← prob_event_or_add_prob_event_and, this, add_zero]

lemma prob_event_or_eq_add' {p q : α → Prop} (h : ∀ x ∈ oa.support, q x → ¬ p x) :
  ⁅λ x, p x ∨ q x | oa⁆ = ⁅p | oa⁆ + ⁅q | oa⁆ :=
have ⁅λ x, p x ∧ q x | oa⁆ = 0 := by simpa only [prob_event_eq_zero_iff, not_and'] using h,
by rw [← prob_event_or_add_prob_event_and, this, add_zero]

lemma prob_event_or_le_add {p q : α → Prop} : ⁅λ x, p x ∨ q x | oa⁆ ≤ ⁅p | oa⁆ + ⁅q | oa⁆ :=
le_of_le_of_eq le_self_add (prob_event_or_add_prob_event_and oa p q)

lemma prob_event_eq_add_cases (p q : α → Prop) :
  ⁅p | oa⁆ = ⁅λ x, p x ∧ q x | oa⁆ + ⁅λ x, p x ∧ ¬ q x | oa⁆ :=
symm (⁅oa⁆.to_outer_measure_apply_inter_add_diff p q)

lemma prob_event_eq_add_cases' (p q : α → Prop) :
  ⁅p | oa⁆ = ⁅λ x, q x ∧ p x | oa⁆ + ⁅λ x, ¬ q x ∧ p x | oa⁆ :=
by simp only [prob_event_eq_add_cases oa p q, and_comm]

lemma prob_event_and_not_eq_sub (p q : α → Prop) :
  ⁅λ x, p x ∧ ¬ q x | oa⁆ = ⁅p | oa⁆ - ⁅λ x, p x ∧ q x | oa⁆ :=
by rw [prob_event_eq_add_cases oa p q, ennreal.add_sub_cancel_left prob_event_ne_top]

lemma prob_event_not_and_eq_sub (p q : α → Prop) :
  ⁅λ x, ¬ p x ∧ q x | oa⁆ = ⁅q | oa⁆ - ⁅λ x, p x ∧ q x | oa⁆ :=
trans (prob_event_ext _ (λ x, and_comm _ _)) (trans (prob_event_and_not_eq_sub oa q p)
  (congr_arg (λ x, _ - x) (prob_event_ext _ (λ x, and_comm (q x) (p x)))))

end bool

end oracle_comp