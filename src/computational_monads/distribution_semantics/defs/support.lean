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

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Set of possible outputs of the computation, allowing for any possible output of the queries.
This will generally correspond to the support of `eval_dist` (see `support_eval_dist`),
but is slightly more general since it doesn't require α finite range. -/
def support : Π {α : Type} (oa : oracle_comp spec α), set α
| _ (pure' α a) := {a}
| _ (query_bind' i t α oa) := ⋃ u, (oa u).support

@[simp] lemma support_return (spec) (a) : (return a : oracle_comp spec α).support = {a} := rfl

lemma support_pure' (spec) (a) : (pure' α a : oracle_comp spec α).support = {a} := rfl

lemma support_pure (spec) (a) : (pure a : oracle_comp spec α).support = {a} := rfl

lemma support_query_bind' (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α) :
  (query_bind' i t α oa).support = ⋃ u, (oa u).support := rfl

@[simp] lemma support_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (oa >>= ob).support = ⋃ α ∈ oa.support, (ob α).support :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa,
  { simp only [pure_bind, support_return, set.mem_singleton_iff, set.Union_Union_eq_left] },
  { simp_rw [bind_assoc, ← query_bind'_eq_query_bind,
      support_query_bind', hoa, set.mem_Union, set.Union_exists],
    exact set.Union_comm _ }
end

lemma support_bind' (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (bind' α β oa ob).support = ⋃ α ∈ oa.support, (ob α).support :=
by rw [oracle_comp.bind'_eq_bind, support_bind]

@[simp] lemma support_query (i : spec.ι) (t : spec.domain i) :
  (query i t).support = set.univ :=
by simp only [query_def, support_query_bind', support_pure',
  set.Union_singleton_eq_range, set.range_id']

/-- If the range of `spec` is a `fintype` then the support is a finite set. -/
lemma support_finite (oa : oracle_comp spec α) : oa.support.finite :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa,
  { exact set.finite_singleton a },
  { simp only [set.finite_Union hoa, support_bind, support_query, set.Union_true] }
end

noncomputable instance support.coe_sort_fintype (oa : oracle_comp spec α) :
  fintype ↥(oa.support) := (support_finite oa).fintype

/-- Since the range of oracles in an `oracle_spec` are required to be nonempty,
we naturally get that the `support` of an `oracle_comp` is nonempty. -/
lemma support_nonempty (oa : oracle_comp spec α) : oa.support.nonempty :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact set.singleton_nonempty a },
  { simp only [oracle_comp.bind'_eq_bind, support_bind,
      set.nonempty_bUnion, exists_prop],
    exact let ⟨a, ha⟩ := hoa in ⟨a, ha, hob a⟩ },
  { simp only [support_query, set.top_eq_univ, set.univ_nonempty] }
end

instance support.coe_sort_inhabited (oa : oracle_comp spec α) : inhabited ↥(oa.support) :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact ⟨⟨a, set.mem_singleton_of_eq rfl⟩⟩ },
  { refine ⟨⟨(hob hoa.1).1.1, _⟩⟩,
    simp only [subtype.val_eq_coe, oracle_comp.bind'_eq_bind, support_bind,
      set.mem_Union, exists_prop],
    exact ⟨hoa.1.1, hoa.1.2, (hob hoa.1).1.2⟩ },
  { rw [support_query],
    exact ⟨⟨default, set.mem_univ _⟩⟩ }
end

lemma support_eq_singleton_iff_forall (oa : oracle_comp spec α) (x) :
  oa.support = {x} ↔ ∀ x' ∈ oa.support, x' = x :=
by simp only [set.eq_singleton_iff_nonempty_unique_mem, oa.support_nonempty, true_and]

lemma support_eq_singleton_iff_subset (oa : oracle_comp spec α) (x) :
  oa.support = {x} ↔ oa.support ⊆ {x} :=
by simp only [support_eq_singleton_iff_forall, set.subset_singleton_iff]

/-- Should be able to automatically derive the support for most simple computations -/
example :
do{ b ← coin, b' ← coin,
    x ← if b then return 0 else return 1,
    y ← return (if b' then 1 else 2),
    z ← if b then return x else return (y - y),
    return (x * y * z) }.support = {0} := by simp

end oracle_comp