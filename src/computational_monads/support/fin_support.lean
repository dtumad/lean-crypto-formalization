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
The resulting `fin_set` is equal to `oracle_comp.support` when coerced to a `set`,
  see `fin_support_eq_support`.

This requires a number of decidability hypotheses for the computation itself.
The need for `oracle_comp.decidable` arises from the need to use `finset.bUnion` for `bind'`.
We also require a `computable` and `finite_range` instance for the `oracle_spec` itself.
Without the `finite_range` instance, the support may be infinite,
  so only `oracle_comp.support` will exist
-/

namespace oracle_comp

open oracle_spec decidable

variables {α β γ : Type} {spec spec' : oracle_spec}
  [computable spec] [computable spec'] [finite_range spec] [finite_range spec']

/-- Version of `fin_support` taking an explicit `decidable` argument instead of an instance -/
def fin_support' : Π {α : Type} (oa : oracle_comp spec α), oa.decidable → finset α
| _ _ (decidable_pure' α a h) := {a}
| _ _ (decidable_bind' α β oa ob hoa hob) := 
  have hβ : decidable_eq β := decidable_eq_of_decidable' (hob $ (inhabited_base oa).1),
  @finset.bUnion α β hβ (fin_support' oa hoa) (λ a, fin_support' (ob a) (hob a))
| _ _ (decidable_query i t) := finset.univ

/-- Compute an explicit `finset` of the elements in `support`,
  assuming `computable` and `finite_range` instances on the `spec`,
  and a `decidable` instance on the `oracle_comp` itself. -/
def fin_support (oa : oracle_comp spec α) [hoa : oa.decidable] : finset α :=
oa.fin_support' hoa

lemma fin_support_def (oa : oracle_comp spec α) [hoa : oa.decidable] :
  oa.fin_support = oa.fin_support' hoa := rfl

lemma mem_fin_support'_iff_mem_support : Π {α : Type} (oa : oracle_comp spec α)
  (hoa : decidable oa) (a : α), a ∈ (fin_support' oa hoa) ↔ a ∈ oa.support
| _ _ (decidable_pure' α a h) α' :=
    by simp [finset.coe_singleton α, support, fin_support']
| _ _ (decidable_bind' α β oa ob hoa hob) b :=
    by simp [fin_support', support, mem_fin_support'_iff_mem_support]
| _ _ (decidable_query i t) u :=
    by simp [support, fin_support']

section support

variables (oa : oracle_comp spec α) (oa' : oracle_comp spec' α) [decidable oa] [decidable oa']
  (a : α) (s : finset α)

/-- Correctness of `fin_support` with respect to `support`, i.e. the two are equal as `set`s -/
lemma mem_fin_support_iff_mem_support : a ∈ oa.fin_support ↔ a ∈ oa.support :=
mem_fin_support'_iff_mem_support oa _ a

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

variables (a a' : α) [decidable_eq α]

@[simp] lemma fin_support_return : (return a : oracle_comp spec α).fin_support = {a} := rfl

lemma mem_fin_support_return_iff : a' ∈ (return a : oracle_comp spec α).fin_support ↔ a' = a :=
finset.mem_singleton

@[simp] lemma fin_support_pure' : (pure' α a : oracle_comp spec α).fin_support = {a} := rfl

lemma mem_fin_support_pure'_iff : a' ∈ (pure' α a : oracle_comp spec α).fin_support ↔ a' = a :=
finset.mem_singleton

lemma fin_support_pure : (pure a : oracle_comp spec α).fin_support = {a} := rfl

lemma mem_fin_support_pure_iff : a' ∈ (pure a : oracle_comp spec α).fin_support ↔ a' = a :=
finset.mem_singleton

end return

section bind

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  [decidable oa] [∀ a, decidable (ob a)] (b : β)

@[simp] lemma fin_support_bind : (oa >>= ob).fin_support = @finset.bUnion α β
  (decidable_eq_of_decidable (oa >>= ob)) oa.fin_support (λ a, (ob a).fin_support) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind,
  finset.coe_bUnion, coe_fin_support_eq_support]

lemma mem_fin_support_bind_iff : b ∈ (oa >>= ob).fin_support ↔
  ∃ a ∈ oa.fin_support, b ∈ (ob a).fin_support :=
by rw [fin_support_bind, finset.mem_bUnion]

@[simp] lemma fin_support_bind' : (bind' α β oa ob).fin_support = @finset.bUnion α β
  (decidable_eq_of_decidable (bind' α β oa ob)) oa.fin_support (λ a, (ob a).fin_support) :=
fin_support_bind oa ob

lemma mem_fin_support_bind'_iff : b ∈ (bind' α β oa ob).fin_support ↔
  ∃ a ∈ oa.fin_support, b ∈ (ob a).fin_support :=
mem_fin_support_bind_iff oa ob b

lemma fin_support_return_bind [decidable_eq α] (a : α) :
  (return a >>= ob).fin_support = (ob a).fin_support :=
by simp only [fin_support_bind, fin_support_return, finset.singleton_bUnion]

lemma mem_fin_support_return_bind_iff [decidable_eq α] (a : α) (b : β) :
  b ∈ (return a >>= ob).fin_support ↔ b ∈ (ob a).fin_support :=
by rw [fin_support_return_bind]

@[simp] lemma fin_support_bind_return [decidable_eq β] (f : α → β) :
  (oa >>= λ a, return (f a)).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, support_bind_return,
  finset.coe_image, coe_fin_support_eq_support]

lemma mem_fin_support_bind_return_iff [decidable_eq β] (f : α → β) (b : β) :
  b ∈ (oa >>= λ a, return (f a)).fin_support ↔ ∃ a ∈ oa.fin_support, f a = b :=
by simp only [fin_support_bind_return, finset.mem_image]

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

@[simp] lemma fin_support_query : (query i t).fin_support = ⊤ := rfl

lemma mem_fin_support_query : u ∈ (query i t).fin_support := finset.mem_univ u

end query

section map

variables [decidable_eq β] (oa : oracle_comp spec α) [decidable oa] (f : α → β) (b : β)

@[simp] lemma fin_support_map : (f <$> oa).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_image,
  support_map, coe_fin_support_eq_support]

lemma mem_fin_support_map_iff : b ∈ (f <$> oa).fin_support ↔ ∃ a ∈ oa.fin_support, f a = b :=
by rw [fin_support_map, finset.mem_image]

end map

section image

variables [decidable_eq β] (oa : oracle_comp spec α) [decidable oa] (f : α → β) (b : β)

lemma coe_image_fin_support_eq_image_support :
  (oa.fin_support.image f : set β) = f '' oa.support :=
by simp only [finset.coe_image, coe_fin_support_eq_support]

lemma image_fin_support_eq_iff_image_support_eq_coe (s : finset β) :
  oa.fin_support.image f = s ↔ f '' oa.support = ↑s :=
by rw [← coe_image_fin_support_eq_image_support, finset.coe_eq_coe_iff]

lemma mem_image_fin_support_iff_mem_image_support :
  b ∈ oa.fin_support.image f ↔ b ∈ f '' oa.support :=
by rw [← finset.mem_coe, coe_image_fin_support_eq_image_support]

end image

end oracle_comp