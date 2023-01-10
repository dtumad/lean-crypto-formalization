/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.support.fin_support

/-!
# Support of Monadic Oracle Constructions

This file defines additional lemmas about `support` applied to constructions
given by a composition of monad operations.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

section return_bind

variables (a : α) (ob : α → oracle_comp spec β) (y : β)

lemma support_return_bind : (return a >>= ob).support = (ob a).support :=
by simp only [support_bind, mem_support_return_iff, set.Union_Union_eq_left]

lemma mem_support_return_bind_iff : y ∈ (return a >>= ob).support ↔ y ∈ (ob a).support :=
by rw [support_return_bind]

variables [decidable_eq α] [∀ a, decidable (ob a)]

lemma fin_support_return_bind : (return a >>= ob).fin_support = (ob a).fin_support :=
by simp only [fin_support_bind, fin_support_return, finset.singleton_bUnion]

lemma mem_fin_support_return_bind_iff :
  y ∈ (return a >>= ob).fin_support ↔ y ∈ (ob a).fin_support :=
by rw [fin_support_return_bind]

end return_bind

section bind_return

variables (oa : oracle_comp spec α) (f : α → β) (y : β)

@[simp] lemma support_bind_return : (oa >>= λ x, return (f x)).support = f '' oa.support :=
calc (f <$> oa).support = ⋃ x ∈ oa.support, {f x} : rfl
  ... = f '' (⋃ x ∈ oa.support, {x}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

lemma mem_support_bind_return_iff :
  y ∈ (oa >>= λ x, return (f x)).support ↔ ∃ x ∈ oa.support, f x = y :=
by simp only [support_bind_return, set.mem_image, exists_prop]

@[simp] lemma support_bind_return_id : (oa >>= return).support = oa.support :=
(support_bind_return oa id).trans (set.image_id oa.support)

variables [decidable oa]

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

end bind_return

section query_bind

variables (i : spec.ι) (t : spec.domain i) (oa : spec.range i → oracle_comp spec α) (x : α)

lemma support_query_bind : (query i t >>= oa).support = ⋃ u, (oa u).support :=
by simp only [support_bind, set.Union_true]

lemma mem_support_query_bind_iff : x ∈ (query i t >>= oa).support ↔ ∃ t, x ∈ (oa t).support :=
by rw [support_query_bind, set.mem_Union]

variables [decidable_eq α] [∀ u, decidable (oa u)]

lemma fin_support_query_bind : (query i t >>= oa).fin_support =
  finset.bUnion finset.univ (λ u, (oa u).fin_support) :=
by {simp only [fin_support_bind, fin_support_query, finset.top_eq_univ], congr}

lemma mem_fin_support_query_bind_iff :
  x ∈ (query i t >>= oa).fin_support ↔ ∃ t, x ∈ (oa t).fin_support :=
by simp only [fin_support_query_bind, finset.mem_bUnion, finset.mem_univ, exists_true_left]

end query_bind

section map

variables (oa : oracle_comp spec α) (f : α → β)  (y : β)

@[simp] lemma support_map : (f <$> oa).support = f '' oa.support :=
support_bind_return oa f

lemma mem_support_map_iff : y ∈ (f <$> oa).support ↔ ∃ x ∈ oa.support, f x = y :=
mem_support_bind_return_iff oa f y

variables [decidable_eq β] [decidable oa]

@[simp] lemma fin_support_map : (f <$> oa).fin_support = oa.fin_support.image f :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_image,
  support_map, coe_fin_support_eq_support]

lemma mem_fin_support_map_iff : y ∈ (f <$> oa).fin_support ↔ ∃ x ∈ oa.fin_support, f x = y :=
by rw [fin_support_map, finset.mem_image]

end map

section map_return

variables (a : α) (f : α → β) (y : β)

lemma support_map_return : (f <$> (return a : oracle_comp spec α)).support = {f a} :=
by simp only [support_map, support_return, set.image_singleton]

lemma mem_support_map_return_iff : y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

variables [decidable_eq α] [decidable_eq β]

lemma fin_support_map_return :
  (f <$> (return a : oracle_comp spec α)).fin_support = {f a} :=
by simp only [fin_support_map, fin_support_return, finset.image_singleton]

lemma mem_fin_support_map_return_iff :
  y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

end map_return

section map_bind

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (g : β → γ) (z : γ)

@[simp] lemma support_map_bind : (g <$> (oa >>= ob)).support =
  ⋃ a ∈ oa.support, g '' (ob a).support :=
by simp_rw [support_map, support_bind, set.image_Union]

lemma mem_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).support ↔
  ∃ x ∈ oa.support, ∃ y ∈ (ob x).support, g y = z :=
by simp only [support_map_bind, set.mem_Union, set.mem_image, exists_prop]

variables [decidable_eq γ] [decidable oa] [∀ x, decidable (ob x)]

@[simp] lemma fin_support_map_bind : (g <$> (oa >>= ob)).fin_support =
  @finset.bUnion α γ (decidable_eq_of_decidable (g <$> (oa >>= ob)))
    oa.fin_support (λ a, (ob a).fin_support.image g) :=
by simp_rw [fin_support_eq_iff_support_eq_coe, finset.coe_bUnion, finset.coe_image,
  coe_fin_support_eq_support, support_map_bind]

lemma mem_fin_support_map_bind_iff : z ∈ (g <$> (oa >>= ob)).fin_support ↔
  ∃ x ∈ oa.fin_support, ∃ y ∈ (ob x).fin_support, g y = z :=
by simp only [fin_support_map_bind, finset.mem_bUnion, finset.mem_image]

end map_bind

section bind_map

variables (oa : oracle_comp spec α) (f : α → β) (oc : β → oracle_comp spec γ) (z : γ)

lemma support_bind_map : ((f <$> oa) >>= oc).support =
  ⋃ x ∈ oa.support, (oc (f x)).support :=
by simp only [support_bind, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

lemma mem_support_bind_map_iff : z ∈ ((f <$> oa) >>= oc).support ↔
  ∃ x ∈ oa.support, z ∈ (oc (f x)).support :=
by simp only [support_bind, set.mem_Union, support_map, set.mem_image,
  set.Union_exists, set.bUnion_and', set.Union_Union_eq_right]

variables [decidable_eq β] [decidable oa] [∀ y, decidable (oc y)]

@[simp] lemma fin_support_bind_map : ((f <$> oa) >>= oc).fin_support = @finset.bUnion α γ
  (decidable_eq_of_decidable ((f <$> oa) >>= oc)) oa.fin_support (λ a, (oc (f a)).fin_support) :=
by simp only [finset.image_bUnion, fin_support_bind, fin_support_map]

lemma mem_fin_support_bind_map_iff : z ∈ ((f <$> oa) >>= oc).fin_support ↔
  ∃ x ∈ oa.fin_support, z ∈ (oc (f x)).fin_support :=
by simp only [fin_support_bind_map, finset.mem_bUnion]

end bind_map

-- TODO: This doesn't really belong in this file
@[simp] lemma support_bind_ite (oa : oracle_comp spec α) (p : α → Prop) [decidable_pred p]
  (f g : α → β) : (oa >>= λ a, return (if p a then f a else g a)).support =
  (f '' {x ∈ oa.support | p x}) ∪ (g '' {x ∈ oa.support | ¬ p x}) :=
begin
  refine set.ext (λ x, _),
  simp only [mem_support_bind_return_iff, set.mem_union,
    set.mem_image, exists_prop, set.mem_sep_iff],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨x, hx⟩ := h,
    by_cases hpx : p x,
    { rw [if_pos hpx] at hx,
      exact or.inl ⟨x, ⟨hx.1, hpx⟩, hx.2⟩ },
    { rw [if_neg hpx] at hx,
      exact or.inr ⟨x, ⟨hx.1, hpx⟩, hx.2⟩ } },
  { cases h with h h,
    { obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := h,
      exact ⟨x, hx, if_pos hx'⟩ },
    { obtain ⟨x, ⟨hx, hx'⟩, rfl⟩ := h,
      exact ⟨x, hx, if_neg hx'⟩ } }
end

@[simp] lemma fin_support_bind_ite [decidable_eq β] (oa : oracle_comp spec α) [oa.decidable]
  (p : α → Prop) [decidable_pred p] (f : α → β) (g : α → β) :
  (oa >>= λ a, return (if p a then f a else g a)).fin_support =
    ((oa.fin_support.filter p).image f) ∪ ((oa.fin_support.filter (not ∘ p)).image g) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind_ite, finset.coe_union,
  finset.coe_image, finset.coe_filter, coe_fin_support_eq_support]

end oracle_comp