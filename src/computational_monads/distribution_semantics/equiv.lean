/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.independence

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

infix ` ≃ₚₑ ` : 50 := dist_equiv

lemma dist_equiv.def : oa ≃ₚₑ oa' ↔ ⁅oa⁆ = ⁅oa'⁆ := iff.rfl

/-- Show that two computations are equivalent by showing every output has the same probability. -/
lemma dist_equiv.ext (h : ∀ x, ⁅= x | oa⁆ = ⁅= x | oa'⁆) : oa ≃ₚₑ oa' := pmf.ext h

lemma dist_equiv.ext_iff (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) :
  oa ≃ₚₑ oa' ↔ ∀ x, ⁅= x | oa⁆ = ⁅= x | oa'⁆ :=
⟨λ h x, congr_fun (congr_arg _ h) x, dist_equiv.ext⟩

instance dist_equiv.is_refl : is_refl (oracle_comp spec α) dist_equiv := ⟨λ x, rfl⟩

/-- More general than regular `symm`, the two computations may have different `oracle_spec`. -/
lemma dist_equiv.symm (h : oa ≃ₚₑ oa') : oa' ≃ₚₑ oa := h.symm

instance dist_equiv.is_symm : is_symm (oracle_comp spec α) dist_equiv := ⟨λ oa oa' h, h.symm⟩

/-- More general than regular `trans`, the three computations may have different `oracle_spec`. -/
lemma dist_equiv.trans (h : oa ≃ₚₑ oa') (h' : oa' ≃ₚₑ oa'') : oa ≃ₚₑ oa'' := h.trans h'

instance dist_equiv.is_trans : is_trans (oracle_comp spec α) dist_equiv :=
⟨λ oa oa' oa'' h h', h.trans h'⟩

lemma dist_equiv.support_eq (h : oa ≃ₚₑ oa') : oa.support = oa'.support :=
(oa.support_eval_dist).symm.trans ((congr_arg pmf.support h).trans oa'.support_eval_dist)

lemma dist_equiv.fin_support_eq [oa.decidable] [oa'.decidable] (h : oa ≃ₚₑ oa') :
  oa.fin_support = oa'.fin_support :=
(fin_support_eq_fin_support_iff_support_eq_support oa oa').2 h.support_eq

lemma dist_equiv.eval_dist_eq (h : oa ≃ₚₑ oa') : ⁅oa⁆ = ⁅oa'⁆ := h

lemma dist_equiv.eval_dist_apply_eq (h : oa ≃ₚₑ oa') (x : α) : ⁅= x | oa⁆ = ⁅= x | oa'⁆ :=
congr_fun (congr_arg _ h) x

lemma dist_equiv.prob_event_eq (h : oa ≃ₚₑ oa') (e : set α) : ⁅e | oa⁆ = ⁅e | oa'⁆ :=
prob_event_eq_of_eval_dist_eq h.eval_dist_eq e

lemma dist_equiv.indep_events_iff (h : oa ≃ₚₑ oa') (es es' : set (set α)) :
  oa.indep_events es es' ↔ oa'.indep_events es es' :=
indep_events_iff_of_eval_dist_eq oa oa' es es' h

lemma dist_equiv.indep_event_iff (h : oa ≃ₚₑ oa') (e e' : set α) :
  oa.indep_event e e' ↔ oa'.indep_event e e' :=
indep_event_iff_of_eval_dist_eq oa oa' e e' h

section return

/-- `return a` has the same distribution as `oa` iff outputs besides `a` have `0` probability. -/
lemma return_dist_equiv_iff (spec : oracle_spec) (a : α) (oa : oracle_comp spec' α) :
  (return a : oracle_comp spec α) ≃ₚₑ oa ↔ ∀ x ≠ a, ⁅= x | oa⁆ = 0 :=
by rw [dist_equiv, eval_dist_return_eq_iff]

@[simp] lemma return_dist_equiv_return_iff (spec spec' : oracle_spec) (a a' : α) :
  (return a : oracle_comp spec α) ≃ₚₑ (return a' : oracle_comp spec' α) ↔ a = a' :=
begin
  simp only [return_dist_equiv_iff, eval_dist_return_apply_eq_zero_iff],
  refine ⟨λ h, _, λ h x hx, h ▸ hx⟩,
  simpa only [ne.def, imp_not_comm, eq_self_iff_true, not_not,
    true_implies_iff, @eq_comm _ a' a] using h a',
end

end return

section bind

/-- If two computations `oa` and `oa'` are distributionally equivalent to each other,
and computations `ob` and `ob'` are equivalent for any input that is an output of `oa`,
then the sequential computations `oa >>= ob` and `oa' >>= ob'` are equivalent. -/
lemma bind_dist_equiv_bind_of_dist_equiv (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (oa' : oracle_comp spec' α) (ob' : α → oracle_comp spec' β) (h : oa ≃ₚₑ oa')
  (h' : ∀ x ∈ oa.support, ob x ≃ₚₑ ob' x) : (oa >>= ob) ≃ₚₑ (oa' >>= ob') :=
sorry

lemma bind_dist_equiv_bind_of_dist_equiv_left (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oa' : oracle_comp spec α) (h : oa ≃ₚₑ oa') :
  (oa >>= ob) ≃ₚₑ (oa' >>= ob) :=
sorry

lemma bind_dist_equiv_bind_of_dist_equiv_right (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (ob' : α → oracle_comp spec β)
  (h' : ∀ x, ob x ≃ₚₑ ob' x) : (oa >>= ob) ≃ₚₑ (oa >>= ob') :=
sorry

end bind

section query

@[simp] lemma query_dist_equiv_query (i : spec.ι) (t t' : spec.domain i) :
  query i t ≃ₚₑ query i t' :=
dist_equiv.ext (λ u, (eval_dist_query_apply i t u).trans (eval_dist_query_apply i t' u).symm)

end query

end oracle_comp

