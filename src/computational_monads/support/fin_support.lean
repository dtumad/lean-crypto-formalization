/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.support.support
import to_mathlib.general

/-!
# Support of an Oracle Computation as a Finset

This file gives an alternative definition of the support of an `oracle_comp`.
Instead of a `set` as with `oracle_comp.support`, we introduce a definition
  `oracle_comp.fin_support` which gives the support as a `finset`.
The resulting `finset` is equal to `oracle_comp.support` when coerced to a `set`,
  see `fin_support_eq_support`.

This requires a number of decidability hypotheses for the computation itself.
The need for `oracle_comp.decidable` arises from the need to use `finset.bUnion` for `bind'`.
This could be avoided by including a `decidable_eq` requirement of the `pure'` constructor,
but this partially destrays the monad structure of `oracle_comp`.
-/

namespace oracle_comp

open oracle_spec decidable

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Compute an explicit `finset` of the elements in `support`,
assuming a `decidable` instance on the `oracle_comp` itself (for `finset.bUnion`). -/
def fin_support : Π {α : Type} (oa : oracle_comp spec α) [decidable oa], finset α
| _ _ (decidable_pure' α a h) := {a}
| _ _ (decidable_bind' α β oa ob hoa hob) :=
  have hβ : decidable_eq β := decidable_eq_of_decidable' (hob $ (inhabited_base oa).1),
  @finset.bUnion α β hβ (@fin_support α oa hoa) (λ a, @fin_support β (ob a) (hob a))
| _ _ (decidable_query i t) := finset.univ

section support

variables (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) [decidable oa] [decidable oa']
  (a : α) (s : finset α)

/-- Correctness of `fin_support` with respect to `support`, i.e. the two are equal as `set` -/
theorem mem_fin_support_iff_mem_support : Π {α : Type} (oa : oracle_comp spec α)
  [hoa : decidable oa] (a : α), a ∈ (@fin_support _ _ _ hoa) ↔ a ∈ oa.support
| _ _ (decidable_pure' α a h) α' :=
    by simp [finset.coe_singleton α, support, fin_support]
| _ _ (decidable_bind' α β oa ob hoa hob) b :=
    by simp [fin_support, support,mem_fin_support_iff_mem_support]
| _ _ (decidable_query i t) u :=
    by simp [support, fin_support]

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

variables [decidable_eq α] (a x : α)

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

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  [decidable oa] [∀ a, decidable (ob a)] (y : β)

@[simp] lemma fin_support_bind : (oa >>= ob).fin_support = @finset.bUnion α β
  (decidable_eq_of_decidable (oa >>= ob)) oa.fin_support (λ a, (ob a).fin_support) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind,
  finset.coe_bUnion, coe_fin_support_eq_support]

lemma mem_fin_support_bind_iff : y ∈ (oa >>= ob).fin_support ↔
  ∃ x ∈ oa.fin_support, y ∈ (ob x).fin_support :=
by rw [fin_support_bind, finset.mem_bUnion]

@[simp] lemma fin_support_bind' : (bind' α β oa ob).fin_support = @finset.bUnion α β
  (decidable_eq_of_decidable (oa >>= ob)) oa.fin_support (λ a, (ob a).fin_support) :=
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