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

/-- Correctness of `fin_support` with respect to `support`, i.e. the two are equal as `set`s -/
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

variables (a x : α) [decidable_eq α]

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
  [decidable oa] [∀ a, decidable (ob a)] (f : α → β) (x a : α) (y : β)

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

lemma fin_support_return_bind [decidable_eq α] :
  (return a >>= ob).fin_support = (ob a).fin_support :=
by simp only [fin_support_bind, fin_support_return, finset.singleton_bUnion]

lemma mem_fin_support_return_bind_iff [decidable_eq α] :
  y ∈ (return a >>= ob).fin_support ↔ y ∈ (ob a).fin_support :=
by rw [fin_support_return_bind]

@[simp] lemma fin_support_bind_return [decidable_eq β] :
  (oa >>= λ a, return (f a)).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, support_bind_return,
  finset.coe_image, coe_fin_support_eq_support]

lemma mem_fin_support_bind_return_iff [decidable_eq β] :
  y ∈ (oa >>= λ a, return (f a)).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by simp only [fin_support_bind_return, finset.mem_image]

@[simp] lemma fin_support_bind_return_id [decidable_eq α] :
  (oa >>= return).fin_support = oa.fin_support :=
(fin_support_bind_return oa id).trans finset.image_id

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (oa : spec.range i → oracle_comp spec α) [∀ u, decidable (oa u)] (x : α)

@[simp] lemma fin_support_query : (query i t).fin_support = ⊤ := rfl

lemma mem_fin_support_query : u ∈ (query i t).fin_support := finset.mem_univ u

lemma fin_support_query_bind [decidable_eq α] :
  (query i t >>= oa).fin_support = finset.bUnion finset.univ (λ u, (oa u).fin_support) :=
by {simp only [fin_support_bind, fin_support_query, finset.top_eq_univ], congr}

lemma mem_fin_support_query_bind_iff [decidable_eq α] :
  x ∈ (query i t >>= oa).fin_support ↔ ∃ t, x ∈ (oa t).fin_support :=
by simp only [fin_support_query_bind, finset.mem_bUnion, finset.mem_univ, exists_true_left]

end query

section map

variables [decidable_eq β] [decidable_eq γ] (oa : oracle_comp spec α) [decidable oa]
  (ob : α → oracle_comp spec β) [∀ a, decidable (ob a)] (oc : β → oracle_comp spec γ)
  [∀ b, decidable (oc b)] (f : α → β) (g : β → γ) (a x : α) (y : β) (z : γ)

@[simp] lemma fin_support_map : (f <$> oa).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_image,
  support_map, coe_fin_support_eq_support]

lemma mem_fin_support_map_iff : y ∈ (f <$> oa).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by rw [fin_support_map, finset.mem_image]

lemma fin_support_map_return [decidable_eq α] :
  (f <$> (return a : oracle_comp spec α)).fin_support = {f a} :=
by simp only [fin_support_map, fin_support_return, finset.image_singleton]

lemma mem_fin_support_map_return_iff [decidable_eq α] :
  y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

@[simp] lemma fin_support_map_bind : (g <$> (oa >>= ob)).fin_support =
  @finset.bUnion α γ (decidable_eq_of_decidable (g <$> (oa >>= ob)))
    oa.fin_support (λ a, (ob a).fin_support.image g) :=
by simp_rw [fin_support_eq_iff_support_eq_coe, finset.coe_bUnion, finset.coe_image,
  coe_fin_support_eq_support, support_map_bind]

lemma mem_fin_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).fin_support ↔
  ∃ x ∈ oa.fin_support, ∃ y ∈ (ob x).fin_support, g y = z :=
by simp only [fin_support_map_bind, finset.mem_bUnion, finset.mem_image]

@[simp] lemma fin_support_bind_map : ((f <$> oa) >>= oc).fin_support = @finset.bUnion α γ
  (decidable_eq_of_decidable ((f <$> oa) >>= oc)) oa.fin_support (λ a, (oc (f a)).fin_support) :=
by simp only [finset.image_bUnion, fin_support_bind, fin_support_map]

lemma mem_fin_support_bind_map_iff : z ∈ ((f <$> oa) >>= oc).fin_support ↔
  ∃ x ∈ oa.fin_support, z ∈ (oc (f x)).fin_support :=
by simp only [fin_support_bind_map, finset.mem_bUnion]

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

@[simp] lemma fin_support_bind_ite [decidable_eq β] (oa : oracle_comp spec α) [oa.decidable]
  (p : α → Prop) [decidable_pred p] (f : α → β) (g : α → β) :
  (oa >>= λ a, return (if p a then f a else g a)).fin_support =
    ((oa.fin_support.filter p).image f) ∪ ((oa.fin_support.filter (not ∘ p)).image g) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind_ite, finset.coe_union,
  finset.coe_image, finset.coe_filter, coe_fin_support_eq_support]

end oracle_comp