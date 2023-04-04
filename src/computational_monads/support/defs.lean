/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import set_theory.cardinal.basic

import computational_monads.oracle_comp

/-!
# Possible Outputs of a Computation

This file defines two functions, `oracle_comp.support` and `oracle_comp.fin_support`,
giving
-/

namespace oracle_comp

open_locale classical

open oracle_spec

variables {α β : Type} {spec : oracle_spec} (oa : oracle_comp spec α)

section support

/-- Set of possible outputs of the computation, allowing for any possible output of the queries.
This will generally correspond to the support of `eval_dist` (see `support_eval_dist`). -/
def support : Π {α : Type} (oa : oracle_comp spec α), set α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := ⋃ α ∈ oa.support, (ob α).support
| _ (query i t) := ⊤

/-- If the range of `spec` is a `fintype` then the support is a finite set. -/
theorem support_finite (oa : oracle_comp spec α) : oa.support.finite :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact set.finite_singleton a },
  { exact hoa.bind (λ a _, hob a)},
  { exact set.finite_univ }
end

noncomputable instance support.coe_sort_fintype (oa : oracle_comp spec α) :
  fintype ↥(oa.support) := (support_finite oa).fintype

lemma default_result_mem_support (oa : oracle_comp spec α) : oa.default_result ∈ oa.support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact set.mem_singleton a },
  {
    simp only [← bind'_eq_bind, support, set.mem_Union],
    refine ⟨oa.default_result, hoa, hob oa.default_result⟩,

  },
  { exact set.mem_univ default }
end

/-- Since the range of oracles in an `oracle_spec` are required to be nonempty,
we naturally get that the `support` of an `oracle_comp` is nonempty. -/
theorem support_nonempty (oa : oracle_comp spec α) : oa.support.nonempty :=
⟨oa.default_result, oa.default_result_mem_support⟩

instance support.coe_sort_inhabited (oa : oracle_comp spec α) : inhabited ↥(oa.support) :=
subtype.inhabited oa.default_result_mem_support

lemma support_eq_singleton_iff_forall (x : α) : oa.support = {x} ↔ ∀ x' ∈ oa.support, x' = x :=
by simp only [set.eq_singleton_iff_nonempty_unique_mem, oa.support_nonempty, true_and]

end support

section fin_support


end fin_support

end oracle_comp