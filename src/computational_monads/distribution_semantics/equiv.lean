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

As an example, distribution wise we have that `⁅g <$> f <$> oa⁆ = ⁅oa⁆.map (g ∘ f)`,
while the equivalence would give `g <$> f <$> oa ≃ₚ (g ∘ f) <$> oa`.
While the former is more specific, it can cause problems when other parts of the proof rely on
using induction on the computation, as this doesn't translate well into `pmf`.
Additionally using the former to talk about e.g. `support` requires additional rewrites to
get the necessary equivalences in terms of sets and not computations.

Note that distributional equivalence is not preserved under simulation via `oracle_comp.simulate`,
as computations with the same distribution may make different oracle calls that are simulated
differently, in term giving computations that behave differently.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

def dist_equiv (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) : Prop := ⁅oa⁆ = ⁅oa'⁆

variables {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}

infix ` ≃ₚₑ ` : 50 := dist_equiv

/-- Show that -/
lemma dist_equiv.ext (h : ∀ x, ⁅oa⁆ x = ⁅oa'⁆ x) : oa ≃ₚₑ oa' := pmf.ext h

lemma dist_equiv.support_eq (h : oa ≃ₚₑ oa') : oa.support = oa'.support :=
(oa.support_eval_dist).symm.trans ((congr_arg pmf.support h).trans oa'.support_eval_dist)

namespace dist_equiv



end dist_equiv

end oracle_comp

