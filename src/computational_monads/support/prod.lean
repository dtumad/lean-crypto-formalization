/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.support.fin_support

/-!
# Support of Computations Involving Prod

This file contains lemmas about `support` and `fin_support` focused on working with `prod` types.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} (oa : oracle_comp spec α)

section bind_mk_fst

variables (f : α → β) (c : γ)

lemma support_bind_prod_mk_fst : (oa >>= λ a, return (f a, c)).support =
  (λ x, (f x, c)) '' oa.support := support_bind_return oa _

lemma mem_support_bind_prod_mk_fst (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).support ↔ x.1 ∈ f '' oa.support ∧ x.2 = c :=
by simp_rw [support_bind_prod_mk_fst, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_right, and_assoc, @eq_comm γ c]

lemma mem_support_bind_prod_mk_fst_id (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, c)).support ↔ x.1 ∈ oa.support ∧ x.2 = c :=
by erw [mem_support_bind_prod_mk_fst, set.image_id]

@[simp] lemma support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] :
  (oa >>= λ a, return (f a, c)).support = prod.fst ⁻¹' (f '' oa.support) :=
set.ext (λ x, by simp_rw [mem_support_bind_prod_mk_fst, set.mem_preimage,
  eq_iff_true_of_subsingleton, and_true])

lemma mem_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ]
  (x : β × γ) : x ∈ (oa >>= λ a, return (f a, c)).support ↔ x.1 ∈ (f '' oa.support) :=
by rw [support_bind_prod_mk_fst_of_subsingleton, set.mem_preimage]

@[simp] lemma support_bind_prod_mk_fst_id_of_subsingleton [subsingleton γ] :
  (oa >>= λ a, return (a, c)).support = prod.fst ⁻¹' oa.support :=
by rw [support_bind_prod_mk_fst_of_subsingleton, set.image_id']

lemma mem_support_bind_prod_mk_fst_id_of_subsingleton [subsingleton γ] (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, c)).support ↔ x.1 ∈ oa.support :=
by rw [mem_support_bind_prod_mk_fst_of_subsingleton, set.image_id']

section fin_support

variables [computable spec] [finite_range spec] [decidable oa] [decidable_eq γ]

lemma fin_support_bind_prod_mk_fst [decidable_eq β] : (oa >>= λ a, return (f a, c)).fin_support =
  oa.fin_support.image (λ x, (f x, c)) := fin_support_bind_return oa _

lemma mem_fin_support_bind_prod_mk_fst [decidable_eq β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).fin_support ↔ x.1 ∈ oa.fin_support.image f ∧ x.2 = c :=
by simp_rw [fin_support_bind_prod_mk_fst, finset.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_right, @eq_comm γ c]

lemma mem_fin_support_bind_prod_mk_fst_id [decidable_eq α] (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, c)).fin_support ↔ x.1 ∈ oa.fin_support ∧ x.2 = c :=
by erw [mem_fin_support_bind_prod_mk_fst, finset.image_id]

@[simp] lemma fin_support_bind_prod_mk_fst_of_subsingleton [decidable_eq β] [subsingleton γ] :
  (oa >>= λ a, return (f a, c)).fin_support = (oa.fin_support.image f).preimage prod.fst
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨h, subsingleton.elim _ _⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk_fst, finset.mem_preimage, finset.mem_image,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, and_true])

lemma mem_fin_support_bind_prod_mk_fst_of_subsingleton [decidable_eq β] [subsingleton γ]
  (x : β × γ) : x ∈ (oa >>= λ a, return (f a, c)).fin_support ↔ x.1 ∈ (oa.fin_support.image f) :=
by rw [fin_support_bind_prod_mk_fst_of_subsingleton, finset.mem_preimage]

@[simp] lemma fin_support_bind_prod_mk_fst_id_of_subsingleton [decidable_eq α] [subsingleton γ] :
  (oa >>= λ a, return (a, c)).fin_support = oa.fin_support.preimage prod.fst
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨h, subsingleton.elim _ _⟩) :=
by rw [fin_support_bind_prod_mk_fst_of_subsingleton, finset.image_id']

lemma mem_fin_support_bind_prod_mk_fst_id_of_subsingleton [decidable_eq α] [subsingleton γ]
  (x : α × γ) : x ∈ (oa >>= λ a, return (a, c)).fin_support ↔ x.1 ∈ oa.fin_support :=
by erw [mem_fin_support_bind_prod_mk_fst_of_subsingleton, finset.image_id]

end fin_support

end bind_mk_fst

section bind_mk_snd

variables (f : α → γ) (b : β)

lemma support_bind_prod_mk_snd : (oa >>= λ a, return (b, f a)).support =
  (λ x, (b, f x)) '' oa.support := support_bind_return oa _

lemma mem_support_bind_prod_mk_snd (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, f a)).support ↔ x.1 = b ∧ x.2 ∈ f '' oa.support :=
by simp_rw [support_bind_prod_mk_snd, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_left, @eq_comm β b, ← and_assoc, and_comm (x.1 = b)]

lemma mem_support_bind_prod_mk_snd_id (x : β × α) :
  x ∈ (oa >>= λ a, return (b, a)).support ↔ x.1 = b ∧ x.2 ∈ oa.support :=
by erw [mem_support_bind_prod_mk_snd, set.image_id]

@[simp] lemma support_bind_prod_mk_snd_of_subsingleton [subsingleton β] :
  (oa >>= λ a, return (b, f a)).support = prod.snd ⁻¹' (f '' oa.support) :=
set.ext (λ x, by simp_rw [mem_support_bind_prod_mk_snd, set.mem_preimage,
  eq_iff_true_of_subsingleton, true_and])

lemma mem_support_bind_prod_mk_snd_of_subsingleton [subsingleton β]
  (x : β × γ) : x ∈ (oa >>= λ a, return (b, f a)).support ↔ x.2 ∈ (f '' oa.support) :=
by rw [support_bind_prod_mk_snd_of_subsingleton, set.mem_preimage]

@[simp] lemma support_bind_prod_mk_snd_id_of_subsingleton [subsingleton β] :
  (oa >>= λ a, return (b, a)).support = prod.snd ⁻¹' oa.support :=
by erw [support_bind_prod_mk_snd_of_subsingleton, set.image_id]

lemma mem_support_bind_prod_mk_snd_id_of_subsingleton [subsingleton β] (x : β × α) :
  x ∈ (oa >>= λ a, return (b, a)).support ↔ x.2 ∈ oa.support :=
by erw [mem_support_bind_prod_mk_snd_of_subsingleton, set.image_id]

section fin_support

variables [computable spec] [finite_range spec] [decidable oa] [decidable_eq β]

lemma fin_support_bind_prod_mk_snd [decidable_eq γ] :
  (oa >>= λ a, return (b, f a)).fin_support = oa.fin_support.image (λ x, (b, f x)) :=
fin_support_bind_return oa _

lemma mem_fin_support_bind_prod_mk_snd [decidable_eq γ] (x : β × γ) :
  x ∈ (oa >>= λ a, return (b, f a)).fin_support ↔ x.1 = b ∧ x.2 ∈ oa.fin_support.image f :=
by simp_rw [fin_support_bind_prod_mk_snd, finset.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_left, @eq_comm β b]

lemma mem_fin_support_bind_prod_mk_snd_id [decidable_eq α] (x : β × α) :
  x ∈ (oa >>= λ a, return (b, a)).fin_support ↔ x.1 = b ∧ x.2 ∈ oa.fin_support :=
by erw [mem_fin_support_bind_prod_mk_snd, finset.image_id]

@[simp] lemma fin_support_bind_prod_mk_snd_of_subsingleton [decidable_eq γ] [subsingleton β] :
  (oa >>= λ a, return (b, f a)).fin_support = (oa.fin_support.image f).preimage prod.snd
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨subsingleton.elim _ _, h⟩) :=
finset.ext (λ x, by simp only [fin_support_bind_prod_mk_snd, finset.mem_preimage, finset.mem_image,
  prod.eq_iff_fst_eq_snd_eq, eq_iff_true_of_subsingleton, true_and])

lemma mem_fin_support_bind_prod_mk_snd_of_subsingleton [decidable_eq γ] [subsingleton β]
  (x : β × γ) : x ∈ (oa >>= λ a, return (b, f a)).fin_support ↔ x.2 ∈ (oa.fin_support.image f) :=
by rw [fin_support_bind_prod_mk_snd_of_subsingleton, finset.mem_preimage]

@[simp] lemma fin_support_bind_prod_mk_snd_id_of_subsingleton [decidable_eq α] [subsingleton β] :
  (oa >>= λ a, return (b, a)).fin_support = oa.fin_support.preimage prod.snd
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨subsingleton.elim _ _, h⟩) :=
by rw [fin_support_bind_prod_mk_snd_of_subsingleton, finset.image_id']

lemma mem_fin_support_bind_prod_mk_snd_id_of_subsingleton [decidable_eq α] [subsingleton β]
  (x : β × α) : x ∈ (oa >>= λ a, return (b, a)).fin_support ↔ x.2 ∈ oa.fin_support :=
by erw [mem_fin_support_bind_prod_mk_snd_of_subsingleton, finset.image_id]

end fin_support

end bind_mk_snd

end oracle_comp