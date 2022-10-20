import computational_monads.support.fin_support

/-!
# Support of Computations Involving Prod

This file contains lemmas about `support` and `fin_support` focused on working with `prod` types.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} (oa : oracle_comp spec α)

section bind_mk_fst

-- TODO!: More compact to write every `simp` tag like this???
@[simp] lemma support_bind_prod_mk_fst (b : β) :
  (oa >>= λ a, return (a, b)).support = (λ x, (x, b)) '' oa.support :=
set.ext (λ x, by simp_rw [support_bind, support_return, set.mem_Union,
  set.mem_singleton_iff, exists_prop, set.mem_image, @eq_comm _ x])

lemma mem_support_bind_prod_mk_fst (b : β) (x : α × β) :
  x ∈ (oa >>= λ a, return (a, b)).support ↔ x.1 ∈ oa.support ∧ x.2 = b :=
begin
  simp_rw [support_bind_prod_mk_fst, set.mem_image, prod.eq_iff_fst_eq_snd_eq],
  exact ⟨λ h, let ⟨i, hi, hi', hb⟩ := h in ⟨hi' ▸ hi, hb.symm⟩, λ h, ⟨x.1, h.1, rfl, h.2.symm⟩⟩
end

@[simp] lemma support_bind_prod_mk_fst_of_subsingleton [subsingleton β] (b : β) :
  (oa >>= λ a, return (a, b)).support = prod.fst ⁻¹' oa.support :=
set.ext (λ x, by simp only [mem_support_bind_prod_mk_fst, set.mem_preimage,
  eq_iff_true_of_subsingleton, and_true])

lemma mem_support_bind_prod_mk_fst_of_subsingleton [subsingleton β] (b : β) (x : α × β) :
  x ∈ (oa >>= λ a, return (a, b)).support ↔ x.1 ∈ oa.support :=
by simp only [support_bind_prod_mk_fst_of_subsingleton, set.mem_preimage]

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