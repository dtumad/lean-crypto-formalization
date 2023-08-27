/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.map

/-!
# Distribution Semantics of Computations on Subsingleton Types

This file gives various lemmas for probabilities of computations `oa : oracle_comp spec α`,
when `α` is a subsingleton type, simplifying many computations.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec α) (oa' : oracle_comp spec' α)

/-- If a type `α` is `subsingleton` then any pair of computations are distributionally equivalent,
so in particular they must necessarilly be just `return oa.default_result`. -/
@[simp, pairwise_dist_equiv] lemma dist_equiv_of_subsingleton [subsingleton α] : oa ≃ₚ oa' :=
subsingleton.elim ⁅oa⁆ ⁅oa'⁆

@[pairwise_dist_equiv] lemma dist_equiv_return_of_subsingleton [subsingleton α] (a : α) :
  oa ≃ₚ (return a : oracle_comp spec α) :=
dist_equiv_of_subsingleton _ _

@[simp_dist_equiv] lemma dist_equiv_return_default_result_of_subsingleton [subsingleton α] :
  oa ≃ₚ return' !spec! oa.default_result :=
dist_equiv_of_subsingleton oa _

lemma support_of_subsingleton [subsingleton α] (x : α) : oa.support = {x} :=
(oa.support_eq_singleton_iff_forall x).2 (λ x hx, subsingleton.elim _ _)

@[simp] lemma support_of_unique [unique α] : oa.support = {default} :=
support_of_subsingleton oa default

lemma fin_support_of_subsingleton [subsingleton α] (x : α) : oa.fin_support = {x} :=
(oa.fin_support_eq_singleton_iff_forall x).2 (λ x hx, subsingleton.elim _ _)

@[simp] lemma fin_support_of_unique [unique α] : oa.fin_support = {default} :=
fin_support_of_subsingleton oa default

@[simp] lemma prob_output_of_subsingleton [subsingleton α] (x : α) : ⁅= x | oa⁆ = 1 :=
((dist_equiv_return_of_subsingleton oa x).prob_output_eq x).trans
  ((prob_output_return_eq_one_iff _ _ _).2 (subsingleton.elim _ _))

lemma prob_event_of_subsingleton_of_nonempty [subsingleton α]
  (e : set α) (h : e.nonempty) : ⁅e | oa⁆ = 1 :=
let ⟨y, hy⟩ := h in trans ((dist_equiv_return_of_subsingleton oa y).prob_event_eq _)
  (prob_event_return_of_mem spec _ hy)

end oracle_comp