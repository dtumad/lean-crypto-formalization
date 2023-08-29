/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.support

/-!
# Support of an Oracle Computation as a Finset

This file gives an alternative definition of the support of an `oracle_comp`.
Instead of a `set` as in `oracle_comp.support` we introduce `oracle_comp.fin_support`,
which gives the support as a `finset`, in a way that is compatible with `oracle_comp.support`.
The resulting `finset` is equal to `oracle_comp.support` when coerced to a `set`,
see `oracle_comp.coe_fin_support_eq_support` and `oracle_comp.fin_support_eq_to_finset_support`.

Note that we open `classical` for this, without which we would need `oracle_comp.decidable`
instances to construct the `bUnion` in the `oracle_comp.bind` case. This is mostly done for
simplicity, but could be generalized if a need arises.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

open_locale classical

/-- Compute an explicit `finset` of possible outputs of a computation.
The members exactly match those of `oracle_comp.support`, and the definition is similar. -/
noncomputable def fin_support : Π {α : Type} (oa : oracle_comp spec α), finset α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := finset.bUnion (fin_support oa) (λ x, fin_support (ob x))
| _ (query i t) := finset.univ

section support

variables (oa : oracle_comp spec α) (s : finset α)

/-- Correctness of `fin_support` with respect to `support`, i.e. the two are equal as `set` -/
lemma mem_fin_support_iff_mem_support (x : α) : x ∈ oa.fin_support ↔ x ∈ oa.support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact finset.mem_singleton.trans (set.mem_singleton_iff) },
  { simp only [← bind'_eq_bind, fin_support, support, finset.mem_bUnion, set.mem_Union, hoa, hob] },
  { simp only [fin_support, support, finset.mem_univ, set.top_eq_univ, set.mem_univ] }
end

lemma mem_fin_support_of_mem_support {x : α} (hx : x ∈ oa.support) : x ∈ oa.fin_support :=
(mem_fin_support_iff_mem_support oa x).2 hx

lemma fin_support_eq_to_finset : oa.fin_support = oa.support.to_finset :=
finset.ext (λ x, by simp only [mem_fin_support_iff_mem_support, set.mem_to_finset])

@[simp] lemma coe_fin_support_eq_support : ↑oa.fin_support = oa.support :=
set.ext (λ a, (mem_fin_support_iff_mem_support oa a))

lemma fin_support_eq_iff_support_eq_coe : oa.fin_support = s ↔ oa.support = ↑s :=
by rw [← coe_fin_support_eq_support, finset.coe_inj]

lemma fin_support_eq_fin_support_iff_support_eq_support (oa' : oracle_comp spec' α) :
  oa.fin_support = oa'.fin_support ↔ oa.support = oa'.support :=
by rw [fin_support_eq_iff_support_eq_coe, coe_fin_support_eq_support]

lemma fin_support_eq_fin_support_of_support_eq_support (oa' : oracle_comp spec' α)
  (h : oa.support = oa'.support) : oa.fin_support = oa'.fin_support :=
(fin_support_eq_fin_support_iff_support_eq_support oa oa').2 h

lemma fin_support_subset_iff_support_subset_coe : oa.fin_support ⊆ s ↔ oa.support ⊆ ↑s :=
by rw [← finset.coe_subset, coe_fin_support_eq_support]

lemma subset_fin_support_iff_coe_subset_support : s ⊆ oa.fin_support ↔ ↑s ⊆ oa.support :=
by rw [← finset.coe_subset, coe_fin_support_eq_support]

lemma support_subset_coe_fin_support : oa.support ⊆ ↑oa.fin_support :=
by rw [coe_fin_support_eq_support oa]

lemma coe_fin_support_subset_support : ↑oa.fin_support ⊆ oa.support :=
by rw [coe_fin_support_eq_support oa]

end support

@[simp] lemma fin_support_return (spec) (a) :
  (return a : oracle_comp spec α).fin_support = {a} := rfl

lemma fin_support_pure' (spec) (a) : (pure' α a : oracle_comp spec α).fin_support = {a} := rfl

lemma fin_support_pure (spec) (a) : (pure a : oracle_comp spec α).fin_support = {a} := rfl

@[simp] lemma fin_support_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (oa >>= ob).fin_support = finset.bUnion oa.fin_support (λ a, (ob a).fin_support) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind,
  finset.coe_bUnion, coe_fin_support_eq_support]

@[simp] lemma fin_support_bind' (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (bind' α β oa ob).fin_support = finset.bUnion oa.fin_support (λ a, (ob a).fin_support) :=
fin_support_bind oa ob

@[simp] lemma fin_support_query (i : spec.ι) (t : spec.domain i) :
  (query i t).fin_support = finset.univ := rfl

/-- The `fin_support` of a computation is never empty (since `support` is never empty). -/
lemma fin_support_nonempty (oa : oracle_comp spec α) : oa.fin_support.nonempty :=
let ⟨x, hx⟩ := oa.support_nonempty in ⟨x, mem_fin_support_of_mem_support oa hx⟩

lemma fin_support_eq_singleton_iff_forall (oa : oracle_comp spec α) (x) :
  oa.fin_support = {x} ↔ ∀ x' ∈ oa.support, x' = x :=
by simp [fin_support_eq_iff_support_eq_coe, support_eq_singleton_iff_forall]

lemma fin_support_eq_singleton_iff_subset (oa : oracle_comp spec α) (x) :
  oa.fin_support = {x} ↔ oa.support ⊆ {x} :=
by simp [fin_support_eq_iff_support_eq_coe, support_eq_singleton_iff_subset]

end oracle_comp