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
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Compute an explicit `finset` of possible outputs of a computation.
The members exactly match those of `oracle_comp.support`, and the definition is similar. -/
def fin_support : Π {α : Type} [decidable_eq α] (oa : oracle_comp spec α), finset α
| _ _ (pure' α a) := {a}
| _ h (query_bind' i t α oa) := @finset.bUnion _ _ h finset.univ (λ u, @fin_support α h (oa u))

section support

variables [decidable_eq α] (oa : oracle_comp spec α) (s : finset α)

/-- Correctness of `fin_support` with respect to `support`, i.e. the two are equal as `set` -/
lemma mem_fin_support_iff_mem_support (x : α) : x ∈ oa.fin_support ↔ x ∈ oa.support :=
begin
  unfreezingI { induction oa using oracle_comp.induction_on' with α a i t α oa hoa },
  { exact finset.mem_singleton.trans set.mem_singleton_iff },
  { simp only [← query_bind'_eq_query_bind, fin_support, support,
      set.mem_Union, finset.mem_bUnion, hoa, finset.mem_univ, exists_true_left] }
end

lemma mem_fin_support_of_mem_support {x : α} (hx : x ∈ oa.support) : x ∈ oa.fin_support :=
(mem_fin_support_iff_mem_support oa x).2 hx

lemma fin_support_eq_to_finset : oa.fin_support = oa.support.to_finset :=
finset.ext (λ x, by simp only [mem_fin_support_iff_mem_support, set.mem_to_finset])

@[simp] lemma coe_fin_support_eq_support : ↑oa.fin_support = oa.support :=
set.ext (λ a, (mem_fin_support_iff_mem_support oa a))

lemma fin_support_eq_iff_support_eq_coe : oa.fin_support = s ↔ oa.support = ↑s :=
by rw [← coe_fin_support_eq_support, finset.coe_inj]

lemma eq_fin_support_iff_coe_eq_support : s = oa.fin_support ↔ ↑s = oa.support :=
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

@[simp] lemma fin_support_return [decidable_eq α] (spec) (a) :
  (return a : oracle_comp spec α).fin_support = {a} := rfl

lemma fin_support_pure' [decidable_eq α] (spec) (a) :
  (pure' α a : oracle_comp spec α).fin_support = {a} := rfl

lemma fin_support_pure [decidable_eq α] (spec) (a) :
  (pure a : oracle_comp spec α).fin_support = {a} := rfl

lemma fin_support_query_bind' [decidable_eq α] (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α) : (query_bind' i t α oa).fin_support =
  finset.bUnion finset.univ (λ u, (oa u).fin_support) := by rw [fin_support]

@[simp] lemma fin_support_bind [decidable_eq α] [decidable_eq β] (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) : (oa >>= ob).fin_support =
  finset.bUnion oa.fin_support (λ a, (ob a).fin_support) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_bind,
  finset.coe_bUnion, coe_fin_support_eq_support]

@[simp] lemma fin_support_bind' [decidable_eq α] [decidable_eq β] (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) : (bind' α β oa ob).fin_support =
  finset.bUnion oa.fin_support (λ a, (ob a).fin_support) :=
fin_support_bind oa ob

@[simp] lemma fin_support_query (i : spec.ι) (t : spec.domain i) :
  (query i t).fin_support = finset.univ :=
by simp only [query_def, fin_support_query_bind', oracle_comp.pure'_eq_return,
  fin_support_return, finset.bUnion_singleton_eq_self]

/-- The `fin_support` of a computation is never empty (since `support` is never empty). -/
lemma fin_support_nonempty [decidable_eq α] (oa : oracle_comp spec α) : oa.fin_support.nonempty :=
let ⟨x, hx⟩ := oa.support_nonempty in ⟨x, mem_fin_support_of_mem_support oa hx⟩

lemma fin_support_eq_singleton_iff_forall [decidable_eq α] (oa : oracle_comp spec α) (x) :
  oa.fin_support = {x} ↔ ∀ x' ∈ oa.support, x' = x :=
by simp [fin_support_eq_iff_support_eq_coe, support_eq_singleton_iff_forall]

lemma fin_support_eq_singleton_iff_subset [decidable_eq α] (oa : oracle_comp spec α) (x) :
  oa.fin_support = {x} ↔ oa.support ⊆ {x} :=
by simp [fin_support_eq_iff_support_eq_coe, support_eq_singleton_iff_subset]

end oracle_comp