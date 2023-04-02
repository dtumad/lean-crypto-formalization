/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.support.monad
import data.finset.preimage

/-!
# Support of Computations Involving Prod

This file contains lemmas about `support` and `fin_support` focused on working with `prod` types.
We also give specialized versions for when one half of the product type is `subsingleton`
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec} (oa : oracle_comp spec α)
  (f : α → β) (g : α → γ) (b : β) (c : γ)

section bind_prod_mk

section support

lemma support_bind_prod_mk : (oa >>= λ a, return (f a, g a)).support =
  (λ a, (f a, g a)) '' oa.support := support_bind_return oa _

lemma support_map_prod_mk : ((λ a, (f a, g a) : α → β × γ) <$> oa).support =
  (λ a, (f a, g a)) '' oa.support := support_map oa _

lemma mem_support_bind_prod_mk (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ y ∈ oa.support, f y = x.1 ∧ g y = x.2 :=
by simp only [support_bind_return, set.mem_image, exists_prop, prod.eq_iff_fst_eq_snd_eq]

lemma mem_support_map_prod_mk (x : β × γ) :
  x ∈ ((λ a, (f a, g a) : α → β × γ) <$> oa).support ↔ ∃ y ∈ oa.support, f y = x.1 ∧ g y = x.2 :=
mem_support_bind_prod_mk oa f g x

lemma mem_support_bind_prod_mk_id_fst (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, g a)).support ↔ x.1 ∈ oa.support ∧ g x.1 = x.2 :=
calc x ∈ (oa >>= λ a, return (a, g a)).support
  ↔ ∃ y, y ∈ oa.support ∧ y = x.1 ∧ g y = x.2 : by simp_rw [mem_support_bind_prod_mk, exists_prop]
  ... ↔ ∃ y, y = x.1 ∧ y ∈ oa.support ∧ g y = x.2 :
    exists_congr (λ y, by simp_rw [and_comm (y ∈ oa.support), and_assoc])
  ... ↔ x.1 ∈ oa.support ∧ g x.1 = x.2 : exists_eq_left

lemma mem_support_bind_prod_mk_id_snd (x : β × α) :
  x ∈ (oa >>= λ a, return (f a, a)).support ↔ x.2 ∈ oa.support ∧ f x.2 = x.1  :=
calc x ∈ (oa >>= λ a, return (f a, a)).support
  ↔ ∃ y, y ∈ oa.support ∧ f y = x.1 ∧ y = x.2 : by simp_rw [mem_support_bind_prod_mk, exists_prop]
  ... ↔ x.2 ∈ oa.support ∧ f x.2 = x.1 : by rw [exists_eq_right_right]

lemma mem_support_bind_prod_mk_fst (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).support ↔ x.1 ∈ f '' oa.support ∧ x.2 = c :=
by simp_rw [support_bind_prod_mk, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_right, and_assoc, @eq_comm γ c]

lemma mem_support_bind_prod_mk_snd (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, g a)).support ↔ x.1 = b ∧ x.2 ∈ g '' oa.support :=
by simp_rw [support_bind_prod_mk, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_left, @eq_comm β b, ← and_assoc, and_comm (x.1 = b)]

end support

section fin_support

variables [decidable oa]

lemma fin_support_bind_prod_mk [decidable_eq β] [decidable_eq γ] :
  (oa >>= λ a, return (f a, g a)).fin_support = oa.fin_support.image (λ a, (f a, g a)) :=
fin_support_bind_return oa _

lemma mem_fin_support_bind_prod_mk [decidable_eq β] [decidable_eq γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).fin_support ↔ ∃ y ∈ oa.fin_support, f y = x.1 ∧ g y = x.2 :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk]

lemma mem_fin_support_bind_prod_mk_id_fst [decidable_eq α] [decidable_eq γ] (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, g a)).fin_support ↔ x.1 ∈ oa.fin_support ∧ g x.1 = x.2 :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_id_fst]

lemma mem_fin_support_bind_prod_mk_id_snd [decidable_eq α] [decidable_eq β] (x : β × α) :
  x ∈ (oa >>= λ a, return (f a, a)).fin_support ↔ x.2 ∈ oa.fin_support ∧ f x.2 = x.1  :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_id_snd]

lemma mem_fin_support_bind_prod_mk_fst [decidable_eq β] [decidable_eq γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).fin_support ↔ x.1 ∈ oa.fin_support.image f ∧ x.2 = c :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_fst,
  set.mem_image, finset.mem_image, exists_prop]

lemma mem_fin_support_bind_prod_mk_snd [decidable_eq β] [decidable_eq γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, g a)).fin_support ↔ x.1 = b ∧ x.2 ∈ oa.fin_support.image g :=
by simp only [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_snd,
  set.mem_image, finset.mem_image, exists_prop]

end fin_support

end bind_prod_mk

section bind_prod_mk_subsingleton

section support

@[simp] lemma support_bind_prod_mk_of_fst_subsingleton [subsingleton β] :
  (oa >>= λ a, return (f a, g a)).support = prod.snd ⁻¹' (g '' oa.support) :=
set.ext (λ x, by simp only [support_bind_prod_mk, set.mem_image, set.mem_preimage,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, true_and])

@[simp] lemma support_bind_prod_mk_of_snd_subsingleton [subsingleton γ] :
  (oa >>= λ a, return (f a, g a)).support = prod.fst ⁻¹' (f '' oa.support) :=
set.ext (λ x, by simp only [support_bind_prod_mk, set.mem_image, set.mem_preimage,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, and_true])

lemma mem_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, f a = x.1 :=
by simp_rw [support_bind_prod_mk_of_snd_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

lemma mem_support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, g a = x.2 :=
by simp_rw [support_bind_prod_mk_of_fst_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

end support

section fin_support

variables [decidable oa]

@[simp] lemma fin_support_bind_prod_mk_fst_of_subsingleton [decidable_eq β] [subsingleton γ] :
  (oa >>= λ a, return (f a, g a)).fin_support = (oa.fin_support.image f).preimage prod.fst
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨h, subsingleton.elim _ _⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk, finset.mem_preimage, finset.mem_image,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, and_true])

@[simp] lemma fin_support_bind_prod_mk_snd_of_subsingleton [decidable_eq γ] [subsingleton β] :
  (oa >>= λ a, return (f a, g a)).fin_support = (oa.fin_support.image g).preimage prod.snd
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨subsingleton.elim _ _, h⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk, finset.mem_preimage, finset.mem_image,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, true_and])

lemma mem_fin_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, f a = x.1 :=
by simp_rw [support_bind_prod_mk_of_snd_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

lemma mem_fin_support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, g a)).support ↔ ∃ a ∈ oa.support, g a = x.2 :=
by simp_rw [support_bind_prod_mk_of_fst_subsingleton, set.mem_preimage, set.mem_image, exists_prop]

end fin_support

end bind_prod_mk_subsingleton

section map_fst_snd

section support

lemma mem_support_map_fst_iff (oab : oracle_comp spec (α × β)) (x : α) :
  x ∈ (prod.fst <$> oab).support ↔ ∃ y, (x, y) ∈ oab.support :=
by simp only [support_map, set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right]

lemma mem_support_map_snd_iff (oab : oracle_comp spec (α × β)) (y : β) :
  y ∈ (prod.snd <$> oab).support ↔ ∃ x, (x, y) ∈ oab.support :=
by simp only [support_map, set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right]

end support

section fin_support

end fin_support

end map_fst_snd

end oracle_comp