/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.independence

/-!
# Distributional Equivalence Between Oracle Computations

This file defines a notion of distributional equivalence between computations.
`dist_equiv oa oa'` (or `oa ≃ₚ oa`) represents two computations for which all values have
the same probability under the denotational semantics provided by `eval_dist`.
Such an equivalence implies equality of `support`, `fin_support`, `eval_dist`, and `prob_event`.
This is especially usefull when it's necessary to avoid "leaving" computations,
as regular probability lemmas will move into the realm of `pmf`, which is sometimes not preferable.

As an example, distribution-wise we have that `⁅g <$> f <$> oa⁆ = ⁅oa⁆.map (g ∘ f)`,
while the equivalence would give `g <$> f <$> oa ≃ₚ (g ∘ f) <$> oa`.
While the former is more specific, it can cause problems when other parts of the proof rely on
using induction on the computation, as this doesn't translate well into `pmf`.
Additionally using the former to talk about e.g. `support` requires additional rewrites to
get the necessary equivalences in terms of sets and not computations.

Note that distributional equivalence is not preserved under simulation via `oracle_comp.simulate`,
as computations with the same distribution may make different oracle calls that are simulated
differently, in term giving computations that behave differently.

TODO: It should be possible to write a tactic similar to `rw` that works for this relation.
As of now, situations requiring `rw` behavior will usually have to apply `dist_equiv.ext` first.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' spec'' : oracle_spec}

/-- Equivalence between computations in terms of the associated probability distribution.
Note that the behavior of equivalent computations may still differ in their oracle queries,
and so this equivalence is not in general preserved under `oracle_comp.simulate`. -/
def dist_equiv (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) : Prop := ⁅oa⁆ = ⁅oa'⁆

variables {oa : oracle_comp spec α} {oa' : oracle_comp spec' α} {oa'' : oracle_comp spec'' α}

infix ` ≃ₚ ` : 50 := dist_equiv

lemma dist_equiv.def : oa ≃ₚ oa' ↔ ⁅oa⁆ = ⁅oa'⁆ := iff.rfl

lemma dist_equiv_of_eq {oa oa' : oracle_comp spec α} (h : oa = oa') : oa ≃ₚ oa' := h ▸ rfl

/-- Show that two computations are equivalent by showing every output has the same probability. -/
@[ext] lemma dist_equiv.ext (h : ∀ x, ⁅= x | oa⁆ = ⁅= x | oa'⁆) : oa ≃ₚ oa' := pmf.ext h

lemma dist_equiv.ext_iff (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) :
  oa ≃ₚ oa' ↔ ∀ x, ⁅= x | oa⁆ = ⁅= x | oa'⁆ :=
⟨λ h x, by rw [prob_output, prob_output, dist_equiv.def.1 h], dist_equiv.ext⟩

@[refl] lemma dist_equiv.refl (oa : oracle_comp spec α) : oa ≃ₚ oa := @rfl (pmf α) ⁅oa⁆

instance dist_equiv.is_refl : is_refl (oracle_comp spec α) (≃ₚ) := ⟨λ x, rfl⟩

lemma dist_equiv.rfl {oa : oracle_comp spec α} : oa ≃ₚ oa := refl oa

@[simp] lemma dist_equiv_self_iff (oa : oracle_comp spec α) : oa ≃ₚ oa ↔ true :=
⟨λ h, true.intro, λ h, dist_equiv.rfl⟩

/-- More general than regular `symm`, the two computations may have different `oracle_spec`. -/
@[symm] lemma dist_equiv.symm (h : oa ≃ₚ oa') : oa' ≃ₚ oa := h.symm

lemma dist_equiv.symm_iff : oa ≃ₚ oa' ↔ oa' ≃ₚ oa := ⟨dist_equiv.symm, dist_equiv.symm⟩

instance dist_equiv.is_symm : is_symm (oracle_comp spec α) dist_equiv := ⟨λ oa oa' h, h.symm⟩

lemma dist_equiv_comm : oa ≃ₚ oa' ↔ oa' ≃ₚ oa := ⟨λ h, h.symm, λ h, h.symm⟩

/-- More general than regular `trans`, the three computations may have different `oracle_spec`. -/
@[trans] lemma dist_equiv.trans (h : oa ≃ₚ oa') (h' : oa' ≃ₚ oa'') : oa ≃ₚ oa'' := h.trans h'

instance dist_equiv.is_trans : is_trans (oracle_comp spec α) dist_equiv :=
⟨λ oa oa' oa'' h h', h.trans h'⟩

instance dist_equiv.is_preorder : is_preorder (oracle_comp spec α) dist_equiv := is_preorder.mk

instance dist_equiv.is_equiv : is_equiv (oracle_comp spec α) dist_equiv := is_equiv.mk

lemma dist_equiv.support_eq (h : oa ≃ₚ oa') : oa.support = oa'.support :=
(oa.support_eval_dist).symm.trans ((congr_arg pmf.support h).trans oa'.support_eval_dist)

lemma dist_equiv.fin_support_eq [decidable_eq α] (h : oa ≃ₚ oa') :
  oa.fin_support = oa'.fin_support :=
(fin_support_eq_fin_support_iff_support_eq_support oa oa').2 h.support_eq

lemma dist_equiv.eval_dist_eq (h : oa ≃ₚ oa') : ⁅oa⁆ = ⁅oa'⁆ := h

lemma dist_equiv.prob_output_eq (h : oa ≃ₚ oa') (x : α) : ⁅= x | oa⁆ = ⁅= x | oa'⁆ :=
(dist_equiv.ext_iff oa oa').1 h x

lemma dist_equiv.eval_dist_apply_eq (h : oa ≃ₚ oa') (x : α) : ⁅oa⁆ x = ⁅oa'⁆ x :=
(dist_equiv.ext_iff oa oa').1 h x

lemma dist_equiv.prob_event_eq (h : oa ≃ₚ oa') (p : α → Prop) : ⁅p | oa⁆ = ⁅p | oa'⁆ :=
prob_event_eq_of_eval_dist_eq h.eval_dist_eq p

lemma dist_equiv.indep_events_iff {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') (es es' : set (α → Prop)) : oa.indep_events es es' ↔ oa'.indep_events es es' :=
by simp only [indep_events_iff, h.prob_event_eq]

lemma dist_equiv.indep_event_iff {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') (p q : α → Prop) : oa.indep_event p q ↔ oa'.indep_event p q :=
by simp only [indep_event_iff, h.prob_event_eq]

end oracle_comp