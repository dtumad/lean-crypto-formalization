/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.eval_dist

/-!
# Output Probabilites for Running Oracle Computations

This file defines a `prob_output` wrapper over `eval_dist` for the probability of a single output,
equal to apply the distribution returned by `eval_dist` at that point.
Having a seperate definition helps prevent the simplifier from getting confused.

We also introduce the notation `⁅= x | oa⁆` for the probability of `x` being returned by `oa`,
under the denotational semantics (in particular assuming queries are answered uniformly at random).

Since showing probabilities are zero and one are very common, we add `@[simp]` tags to a number
of lemmas that have additional hypotheses. This allows the simplifier to use them if e.g.
`x ∉ oa.support` is given to the simplifier in showing that `⁅= x | oa⁆ = 0`.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

noncomputable def prob_output (oa : oracle_comp spec α) (x : α) := ⁅oa⁆ x

notation `⁅=` x `|` oa `⁆` := prob_output oa x

lemma prob_output.def (oa : oracle_comp spec α) (x : α) : ⁅= x | oa⁆ = ⁅oa⁆ x := rfl

lemma eval_dist.prob_output_ext_iff {oa : oracle_comp spec α} {oa' : oracle_comp spec' α} :
  ⁅oa⁆ = ⁅oa'⁆ ↔ ∀ x, ⁅= x | oa⁆ = ⁅= x | oa'⁆ := eval_dist.ext_iff _ _

lemma eval_dist.prob_output_ext (oa : oracle_comp spec α) (oa' : oracle_comp spec' α)
  (h : ∀ x, ⁅= x | oa⁆ = ⁅= x | oa'⁆) : ⁅oa⁆ = ⁅oa'⁆ := eval_dist.ext _ _ h

/-- Have the simplifier tend towards using `prob_output` rather than an applied `eval_dist`-/
@[simp] lemma eval_dist_apply_eq_prob_output (oa : oracle_comp spec α)
  (x : α) : ⁅oa⁆ x = ⁅= x | oa⁆ := rfl

@[simp] lemma prob_output_le_one (oa : oracle_comp spec α) (x : α) :
  ⁅= x | oa⁆ ≤ 1 := pmf.coe_le_one ⁅oa⁆ x

@[simp] lemma prob_output_ne_top (oa : oracle_comp spec α) (x : α) :
  ⁅= x | oa⁆ ≠ ∞ := ne_top_of_le_ne_top ennreal.one_ne_top (oa.prob_output_le_one x)

@[simp] lemma prob_output_lt_top (oa : oracle_comp spec α) (x : α) :
  ⁅= x | oa⁆ < ∞ := lt_of_le_of_ne le_top (oa.prob_output_ne_top x)

@[simp] lemma prob_output_le_top (oa : oracle_comp spec α) (x : α) :
  ⁅= x | oa⁆ ≤ ∞ := le_of_lt (oa.prob_output_lt_top x)

@[simp] lemma tsum_prob_output (oa : oracle_comp spec α) : ∑' x, ⁅= x | oa⁆ = 1 := ⁅oa⁆.tsum_coe

section eq_zero

variables (oa : oracle_comp spec α) (x : α)

@[simp] lemma prob_output_eq_zero_iff : ⁅= x | oa⁆ = 0 ↔ x ∉ oa.support :=
by rw [prob_output, pmf.apply_eq_zero_iff, support_eval_dist]

lemma prob_output_eq_zero_iff' [decidable_eq α] : ⁅= x | oa⁆ = 0 ↔ x ∉ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, prob_output_eq_zero_iff]

@[simp] lemma prob_output_ne_zero_iff : ⁅= x | oa⁆ ≠ 0 ↔ x ∈ oa.support :=
by rw [ne.def, prob_output_eq_zero_iff, set.not_not_mem]

lemma prob_output_ne_zero_iff' [decidable_eq α] : ⁅= x | oa⁆ ≠ 0 ↔ x ∈ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, prob_output_ne_zero_iff]

variables {oa x}

lemma prob_output_eq_zero (h : x ∉ oa.support) :
  ⁅= x | oa⁆ = 0 := (prob_output_eq_zero_iff oa x).2 h

lemma prob_output_eq_zero' [decidable_eq α] (h : x ∉ oa.fin_support) :
  ⁅= x | oa⁆ = 0 := (prob_output_eq_zero_iff' oa x).2 h

lemma prob_output_ne_zero (h : x ∈ oa.support) : ⁅= x | oa⁆ ≠ 0 :=
(prob_output_ne_zero_iff oa x).2 h

lemma prob_output_ne_zero' [decidable_eq α] (h : x ∈ oa.fin_support) : ⁅= x | oa⁆ ≠ 0 :=
(prob_output_ne_zero_iff' oa x).2 h

end eq_zero

section eq_one

variables (oa : oracle_comp spec α) (x : α)

lemma prob_output_eq_one_iff : ⁅= x | oa⁆ = 1 ↔ oa.support = {x} :=
by rw [prob_output, pmf.apply_eq_one_iff, support_eval_dist oa]

lemma prob_output_eq_one_iff' [decidable_eq α] : ⁅= x | oa⁆ = 1 ↔ oa.fin_support = {x} :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_singleton, prob_output_eq_one_iff]

@[simp] lemma prob_output_eq_one_iff_subset : ⁅= x | oa⁆ = 1 ↔ oa.support ⊆ {x} :=
(prob_output_eq_one_iff oa x).trans (set.nonempty.subset_singleton_iff $ support_nonempty oa).symm

lemma prob_output_eq_one_iff_subset' [decidable_eq α] : ⁅= x | oa⁆ = 1 ↔ oa.fin_support ⊆ {x} :=
by rw [fin_support_subset_iff_support_subset_coe, finset.coe_singleton,
  prob_output_eq_one_iff_subset]

variables {oa x}

@[simp] lemma prob_output_eq_one (h : oa.support = {x}) :
  ⁅= x | oa⁆ = 1 := (prob_output_eq_one_iff oa x).2 h

@[simp] lemma prob_output_eq_one' [decidable_eq α] (h : oa.fin_support = {x}) :
  ⁅= x | oa⁆ = 1 := (prob_output_eq_one_iff' oa x).2 h

@[simp] lemma prob_output_eq_one_of_subset (h : oa.support ⊆ {x}) :
  ⁅= x | oa⁆ = 1 := (prob_output_eq_one_iff_subset oa x).2 h

@[simp] lemma prob_output_eq_one_of_subset' [decidable_eq α] (h : oa.fin_support ⊆ {x}) :
  ⁅= x | oa⁆ = 1 := (prob_output_eq_one_iff_subset' oa x).2 h

end eq_one

section pos

variables (oa : oracle_comp spec α) (x : α)

@[simp] lemma prob_output_pos_iff : 0 < ⁅= x | oa⁆ ↔ x ∈ oa.support :=
by rw [pos_iff_ne_zero, prob_output_ne_zero_iff]

lemma prob_output_pos_iff' [decidable_eq α] : 0 < ⁅= x | oa⁆ ↔ x ∈ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, prob_output_pos_iff]

variables {oa} {x}

@[simp] lemma prob_output_pos (h : x ∈ oa.support) :
  0 < ⁅= x | oa⁆ := (prob_output_pos_iff oa x).2 h

@[simp] lemma prob_output_pos' [decidable_eq α] (h : x ∈ oa.fin_support) :
  0 < ⁅= x | oa⁆ := (prob_output_pos_iff' oa x).2 h

end pos

end oracle_comp