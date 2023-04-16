/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import set_theory.cardinal.basic
import computational_monads.oracle_comp

/-!
# Support of an Oracle Computation

This file defines the support of an `oracle_comp`, a `set` of possible outputs of the computation.
  We assume that oracle queries could return any possible value in their range.
This aligns with `pmf.support` for the distribution semantics of `oracle_comp.eval_dist`.

For `return` we set the support to be the singleton set of the return value.
For `>>=` we set the support to be the union over the support of the first computation
of the support of the second computation with that output as its input.
For `query` we simply set the support to be the set of all elements in the oracle's output type. -/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec: oracle_spec} (a : α)
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (i : spec.ι) (t : spec.domain i) (u : spec.range i) (x : α) (y : β)

/-- Set of possible outputs of the computation, allowing for any possible output of the queries.
This will generally correspond to the support of `eval_dist` (see `support_eval_dist`),
but is slightly more general since it doesn't require α finite range. -/
def support : Π {α : Type} (oa : oracle_comp spec α), set α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := ⋃ α ∈ oa.support, (ob α).support
| _ (query i t) := ⊤

variable (spec)

@[simp] lemma support_return : (return a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_return_iff : x ∈ (return a : oracle_comp spec α).support ↔ x = a := iff.rfl

lemma mem_support_return_self : x ∈ (return x : oracle_comp spec α).support := set.mem_singleton x

lemma support_pure' : (pure' α a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_pure'_iff : x ∈ (pure' α a : oracle_comp spec α).support ↔ x = a := iff.rfl

lemma mem_support_pure'_self : x ∈ (pure' α x : oracle_comp spec α).support := set.mem_singleton x

lemma support_pure : (pure a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_pure_iff : x ∈ (pure a : oracle_comp spec α).support ↔ x = a := iff.rfl

lemma mem_support_pure_self : x ∈ (pure x : oracle_comp spec α).support := set.mem_singleton x

variable {spec}

@[simp] lemma support_bind : (oa >>= ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

lemma mem_support_bind_iff : y ∈ (oa >>= ob).support ↔ ∃ x ∈ oa.support, y ∈ (ob x).support :=
by simp_rw [support_bind, set.mem_Union]

lemma support_bind' : (bind' α β oa ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

lemma mem_support_bind'_iff : y ∈ (bind' α β oa ob).support ↔
  ∃ x ∈ oa.support, y ∈ (ob x).support := by simp_rw [support_bind', set.mem_Union]

@[simp] lemma support_query : (query i t).support = ⊤ := rfl

lemma mem_support_query : u ∈ (query i t).support := set.mem_univ u

/-- If the range of `spec` is a `fintype` then the support is a finite set. -/
theorem support_finite (oa : oracle_comp spec α) : oa.support.finite :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact set.finite_singleton a },
  { exact hoa.bind (λ a _, hob a)},
  { exact set.finite_univ }
end

noncomputable instance support.coe_sort_fintype (oa : oracle_comp spec α) :
  fintype ↥(oa.support) := (support_finite oa).fintype

/-- Since the range of oracles in an `oracle_spec` are required to be nonempty,
we naturally get that the `support` of an `oracle_comp` is nonempty. -/
theorem support_nonempty (oa : oracle_comp spec α) : oa.support.nonempty :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact set.singleton_nonempty a },
  { simp only [bind'_eq_bind, support_bind, set.nonempty_bUnion, exists_prop],
    exact let ⟨a, ha⟩ := hoa in ⟨a, ha, hob a⟩ },
  { simp only [support_query, set.top_eq_univ, set.univ_nonempty] }
end

instance support.coe_sort_inhabited (oa : oracle_comp spec α) : inhabited ↥(oa.support) :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact ⟨⟨a, mem_support_pure_self spec a⟩⟩ },
  { refine ⟨⟨(hob hoa.1).1.1, _⟩⟩,
    simp only [subtype.val_eq_coe, bind'_eq_bind, support_bind, set.mem_Union, exists_prop],
    exact ⟨hoa.1.1, hoa.1.2, (hob hoa.1).1.2⟩ },
  { exact ⟨⟨default, mem_support_query i t default⟩⟩ }
end

lemma support_eq_singleton_iff_forall : oa.support = {x} ↔ ∀ x' ∈ oa.support, x' = x :=
by simp only [set.eq_singleton_iff_nonempty_unique_mem, oa.support_nonempty, true_and]

lemma support_eq_singleton_iff_subset : oa.support = {x} ↔ oa.support ⊆ {x} :=
by simp only [support_eq_singleton_iff_forall, set.subset_singleton_iff]

/-- Should be able to automatically derive the support for most simple computations -/
example :
do{ β ← coin, β' ← coin,
    x ← if β then return 0 else return 1,
    y ← return (if β' then 1 else 0),
    z ← if β then return x else return (y - y),
    return (x * y * z) }.support = {0} := by simp

end oracle_comp