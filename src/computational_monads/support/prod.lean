import computational_monads.support.fin_support

/-!
# Support of Computations Involving Prod

This file contains lemmas about `support` and `fin_support` focused on working with `prod` types.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} (oa : oracle_comp spec α)

section bind_mk_fst

lemma support_bind_prod_mk_fst (f : α → β) (c : γ) :
  (oa >>= λ a, return (f a, c)).support = (λ x, (f x, c)) '' oa.support :=
support_bind_return oa _

lemma mem_support_bind_prod_mk_fst (f : α → β) (c : γ) (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).support ↔ x.1 ∈ f '' oa.support ∧ x.2 = c :=
by simp_rw [support_bind_prod_mk_fst, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_right, and_assoc, @eq_comm γ c]

lemma mem_support_bind_prod_mk_fst_id (c : γ) (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, c)).support ↔ x.1 ∈ oa.support ∧ x.2 = c :=
by erw [mem_support_bind_prod_mk_fst, set.image_id]

@[simp] lemma support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (f : α → β) (c : γ) :
  (oa >>= λ a, return (f a, c)).support = prod.fst ⁻¹' (f '' oa.support) :=
set.ext (λ x, by simp_rw [mem_support_bind_prod_mk_fst, set.mem_preimage,
  eq_iff_true_of_subsingleton, and_true])

@[simp] lemma support_bind_prod_mk_fst_id_of_subsingleton [subsingleton γ] (c : γ) :
  (oa >>= λ a, return (a, c)).support = prod.fst ⁻¹' oa.support :=
by erw [support_bind_prod_mk_fst_of_subsingleton, set.image_id]

lemma mem_support_bind_prod_mk_fst_of_subsingleton [subsingleton γ] (f : α → β) (c : γ)
  (x : β × γ) : x ∈ (oa >>= λ a, return (f a, c)).support ↔ x.1 ∈ (f '' oa.support) :=
by rw [support_bind_prod_mk_fst_of_subsingleton, set.mem_preimage]

lemma mem_support_bind_prod_mk_fst_id_of_subsingleton [subsingleton γ] (c : γ) (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, c)).support ↔ x.1 ∈ oa.support :=
by erw [mem_support_bind_prod_mk_fst_of_subsingleton, set.image_id]

section fin_support

variables [computable spec] [finite_range spec] [decidable oa] [decidable_eq γ] (f : α → β) (c : γ)

lemma fin_support_bind_prod_mk_fst [decidable_eq β] :
  (oa >>= λ a, return (f a, c)).fin_support = oa.fin_support.image (λ x, (f x, c)) :=
fin_support_bind_return oa _

lemma mem_fin_support_bind_prod_mk_fst [decidable_eq β] (x : β × γ) :
  x ∈ (oa >>= λ a, return (f a, c)).fin_support ↔ x.1 ∈ oa.fin_support.image f ∧ x.2 = c :=
by simp_rw [fin_support_bind_prod_mk_fst, finset.mem_image, prod.eq_iff_fst_eq_snd_eq,
  ← exists_and_distrib_right, @eq_comm γ c]

lemma mem_fin_support_bind_prod_mk_fst_id [decidable_eq α] (x : α × γ) :
  x ∈ (oa >>= λ a, return (a, c)).fin_support ↔ x.1 ∈ oa.fin_support ∧ x.2 = c :=
by erw [mem_fin_support_bind_prod_mk_fst, finset.image_id]

lemma mem_fin_support_bind_prod_mk_fst_of_subsingleton [decidable_eq β] [subsingleton γ]
  (f : α → β) (c : γ)
  (x : β × γ) : x ∈ (oa >>= λ a, return (f a, c)).fin_support ↔ x.1 ∈ (oa.fin_support.image f) :=
by rw [mem_fin_support_iff_mem_support, mem_support_bind_prod_mk_fst_of_subsingleton,
  mem_image_fin_support_iff_mem_image_support]

lemma mem_fin_support_bind_prod_mk_fst_id_of_subsingleton [decidable_eq α] [subsingleton γ]
  (x : α × γ) : x ∈ (oa >>= λ a, return (a, c)).fin_support ↔ x.1 ∈ oa.fin_support :=
by erw [mem_fin_support_bind_prod_mk_fst_of_subsingleton, finset.image_id]

end fin_support

end bind_mk_fst




section bind_mk_snd

@[simp] lemma support_bind_prod_mk_snd (b : β) :
  (oa >>= λ a, return (b, a)).support = (λ x, (b, x)) '' oa.support :=
set.ext (λ x, by simp_rw [support_bind, support_return, set.mem_Union,
  set.mem_singleton_iff, exists_prop, set.mem_image, @eq_comm _ x])

lemma mem_support_bind_prod_mk_snd (b : β) (x : β × α) :
  x ∈ (oa >>= λ a, return (b, a)).support ↔ x.2 ∈ oa.support ∧ x.1 = b :=
begin
  simp_rw [support_bind_prod_mk_snd, set.mem_image, prod.eq_iff_fst_eq_snd_eq],
  exact ⟨λ h, let ⟨i, hi, hb, hi'⟩ := h in ⟨hi' ▸ hi, hb.symm⟩, λ h, ⟨x.2, h.1, h.2.symm, rfl⟩⟩
end

@[simp] lemma support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (b : β) :
  (oa >>= λ a, return (b, a)).support = prod.snd ⁻¹' oa.support :=
set.ext (λ x, by simp only [mem_support_bind_prod_mk_snd, set.mem_preimage,
  eq_iff_true_of_subsingleton, and_true])

lemma mem_support_bind_prod_mk_snd_of_subsingleton [subsingleton β] (b : β) (x : β × α) :
  x ∈ (oa >>= λ a, return (b, a)).support ↔ x.2 ∈ oa.support :=
by simp only [support_bind_prod_mk_snd_of_subsingleton, set.mem_preimage]

end bind_mk_snd

end oracle_comp