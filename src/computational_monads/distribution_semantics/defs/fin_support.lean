/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.support
import to_mathlib.general

/-!
# Support of an Oracle Computation as a Finset

This file gives an alternative definition of the support of an `oracle_comp`.
Instead of a `set` as in `oracle_comp.support` we introduce `oracle_comp.fin_support`,
which gives the support as a `finset`, in a way that is compatible with `oracle_comp.support`.
The resulting `finset` is equal to `oracle_comp.support` when coerced to a `set`,
see `oracle_comp.coe_fin_support_eq_support` and `oracle_comp.fin_support_eq_to_finset_support`.
Note that we open `classical` for this, without which we would need `oracle_comp.decidable`.
This is done for simplicity, as classical seems like a minimal hypothesis. TODO
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

variables (oa : oracle_comp spec α) (oa' : oracle_comp spec' α)
  (a : α) (s : finset α)

/-- Correctness of `fin_support` with respect to `support`, i.e. the two are equal as `set` -/
theorem mem_fin_support_iff_mem_support (oa : oracle_comp spec α) (x : α) :
  x ∈ oa.fin_support ↔ x ∈ oa.support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact finset.mem_singleton.trans (set.mem_singleton_iff) },
  { simp only [← bind'_eq_bind, fin_support, support, finset.mem_bUnion, set.mem_Union, hoa, hob] },
  { simp only [fin_support, support, finset.mem_univ, set.top_eq_univ, set.mem_univ] }
end

lemma fin_support_eq_to_finset : oa.fin_support = oa.support.to_finset :=
finset.ext (λ x, by simp only [mem_fin_support_iff_mem_support, set.mem_to_finset])

@[simp] theorem coe_fin_support_eq_support : ↑oa.fin_support = oa.support :=
set.ext (λ a, (mem_fin_support_iff_mem_support oa a))

lemma fin_support_eq_iff_support_eq_coe : oa.fin_support = s ↔ oa.support = ↑s :=
by rw [← coe_fin_support_eq_support, finset.coe_inj]

lemma fin_support_eq_fin_support_iff_support_eq_support :
  oa.fin_support = oa'.fin_support ↔ oa.support = oa'.support :=
by rw [fin_support_eq_iff_support_eq_coe, coe_fin_support_eq_support]

lemma fin_support_subset_iff_support_subset_coe : oa.fin_support ⊆ s ↔ oa.support ⊆ ↑s :=
by rw [← finset.coe_subset, coe_fin_support_eq_support]

lemma subset_fin_support_iff_coe_subset_support : s ⊆ oa.fin_support ↔ ↑s ⊆ oa.support :=
by rw [← finset.coe_subset, coe_fin_support_eq_support]

lemma support_subset_coe_fin_support : oa.support ⊆ ↑oa.fin_support :=
by rw [coe_fin_support_eq_support oa]

lemma coe_fin_support_subset_support : ↑oa.fin_support ⊆ oa.support :=
by rw [coe_fin_support_eq_support oa]

end support

section return

variables (a x : α)

@[simp] lemma fin_support_return : (return a : oracle_comp spec α).fin_support = {a} := rfl

lemma mem_fin_support_return_iff : x ∈ (return a : oracle_comp spec α).fin_support ↔ x = a :=
finset.mem_singleton

lemma mem_fin_support_return_self : x ∈ (return x : oracle_comp spec α).fin_support :=
finset.mem_singleton_self x

@[simp] lemma fin_support_pure' : (pure' α a : oracle_comp spec α).fin_support = {a} := rfl

lemma mem_fin_support_pure'_iff : x ∈ (pure' α a : oracle_comp spec α).fin_support ↔ x = a :=
finset.mem_singleton

lemma mem_fin_support_pure'_self : x ∈ (pure' α x : oracle_comp spec α).fin_support :=
finset.mem_singleton_self x

lemma fin_support_pure : (pure a : oracle_comp spec α).fin_support = {a} := rfl

lemma mem_fin_support_pure_iff : x ∈ (pure a : oracle_comp spec α).fin_support ↔ x = a :=
finset.mem_singleton

lemma mem_fin_support_pure_self : x ∈ (pure x : oracle_comp spec α).fin_support :=
finset.mem_singleton_self x

end return

section bind

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (y : β)

@[simp] lemma fin_support_bind :
  (oa >>= ob).fin_support = finset.bUnion oa.fin_support (λ a, (ob a).fin_support) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind,
  finset.coe_bUnion, coe_fin_support_eq_support]

lemma mem_fin_support_bind_iff : y ∈ (oa >>= ob).fin_support ↔
  ∃ x ∈ oa.fin_support, y ∈ (ob x).fin_support :=
by rw [fin_support_bind, finset.mem_bUnion]

@[simp] lemma fin_support_bind' :
  (bind' α β oa ob).fin_support = finset.bUnion oa.fin_support (λ a, (ob a).fin_support) :=
fin_support_bind oa ob

lemma mem_fin_support_bind'_iff : y ∈ (bind' α β oa ob).fin_support ↔
  ∃ x ∈ oa.fin_support, y ∈ (ob x).fin_support :=
mem_fin_support_bind_iff oa ob y

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

@[simp] lemma fin_support_query : (query i t).fin_support = ⊤ := rfl

lemma mem_fin_support_query : u ∈ (query i t).fin_support := finset.mem_univ u

end query

end oracle_comp