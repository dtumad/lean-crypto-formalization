/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import set_theory.cardinal.basic
import computational_monads.oracle_comp

/-!
# Support of an Oracle Computation

This file defines the support of an `oracle_comp`, a `set` of possible outputs of the computation.
  We assume that oracle queries could return any possible value in their range.
This aligns with `pmf.support` for the distribution semantics of `oracle_comp.eval_dist`.

For `return` we set the support to be the singleton set of the return value.
For `>>=` we set the support to be the union over the support of the first computation
of the support of the second computation with that output as its input.
For `query` we simply set the support to be the set of all elements in the oracle's output type.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec: oracle_spec}

/-- Set of possible outputs of the computation, allowing for any possible output of the queries.
This will generally correspond to the support of `eval_dist` (see `support_eval_dist`),
but is slightly more general since it doesn't require α finite range. -/
def support : Π {α : Type} (oa : oracle_comp spec α), set α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := ⋃ α ∈ oa.support, (ob α).support
| _ (query i t) := ⊤

section return

variables (spec) (a x : α)

@[simp] lemma support_return : (return a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_return_iff : x ∈ (return a : oracle_comp spec α).support ↔ x = a :=
set.mem_singleton_iff

lemma support_pure' : (pure' α a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_pure'_iff : x ∈ (pure' α a : oracle_comp spec α).support ↔ x = a :=
mem_support_return_iff spec a x

lemma support_pure : (pure a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_pure_iff : x ∈ (pure a : oracle_comp spec α).support ↔ x = a :=
set.mem_singleton_iff

end return

section bind

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (x : β)

@[simp] lemma support_bind : (oa >>= ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

lemma mem_support_bind_iff : x ∈ (oa >>= ob).support ↔
  ∃ y ∈ oa.support, x ∈ (ob y).support := by simp_rw [support_bind, set.mem_Union]

lemma support_bind' : (bind' α β oa ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

lemma mem_support_bind'_iff : x ∈ (bind' α β oa ob).support ↔
  ∃ a ∈ oa.support, x ∈ (ob a).support := by simp_rw [support_bind', set.mem_Union]

lemma support_return_bind (a : α) (ob : α → oracle_comp spec β) :
  (return a >>= ob).support = (ob a).support :=
by simp only [support_bind, mem_support_pure_iff, set.Union_Union_eq_left]

lemma mem_support_return_bind_iff (a : α) (ob : α → oracle_comp spec β) (b : β) :
  b ∈ (return a >>= ob).support ↔ b ∈ (ob a).support := by rw [support_return_bind]

@[simp] lemma support_bind_return (oa : oracle_comp spec α) (f : α → β) :
  (oa >>= λ a, return (f a)).support = f '' oa.support :=
calc (f <$> oa).support = ⋃ α ∈ oa.support, {f α} : rfl
  ... = f '' (⋃ α ∈ oa.support, {α}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

lemma mem_support_bind_return_iff (oa : oracle_comp spec α) (f : α → β) (b : β) :
  b ∈ (oa >>= λ a, return (f a)).support ↔ ∃ a ∈ oa.support, f a = b :=
by simp only [support_bind_return, set.mem_image, exists_prop]

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

@[simp] lemma support_query : (query i t).support = ⊤ := rfl

lemma mem_support_query_iff : u ∈ (query i t).support := set.mem_univ u

end query

section map

variables (f : α → β) (g : β → γ) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (a x : α) (b y : β) (c : γ)

@[simp] lemma support_map : (f <$> oa).support = f '' oa.support := support_bind_return oa f

lemma mem_support_map_iff : b ∈ (f <$> oa).support ↔ ∃ a ∈ oa.support, f a = b :=
mem_support_bind_return_iff oa f b

lemma support_map_return : (f <$> (return a : oracle_comp spec α)).support = {f a} :=
by simp only [support_map, support_return, set.image_singleton]

lemma mem_support_return : y ∈ (f <$> (return a : oracle_comp spec α)).support ↔ y = f a :=
by simp only [support_map, support_return, set.image_singleton, set.mem_singleton_iff]

@[simp] lemma support_map_bind : (g <$> (oa >>= ob)).support =
  ⋃ a ∈ oa.support, g '' (ob a).support :=
by simp_rw [support_map, support_bind, set.image_Union]

lemma mem_support_map_bind_iff : c ∈ (g <$> (oa >>= ob)).support ↔
  ∃ a ∈ oa.support, ∃ b ∈ (ob a).support, g b = c :=
by simp only [support_map_bind, set.mem_Union, set.mem_image, exists_prop]

end map

/-- If the range of `spec` is a `fintype` then the support is a finite set. -/
theorem support_finite [spec.finite_range] (oa : oracle_comp spec α) : oa.support.finite :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact set.finite_singleton a },
  { exact hoa.bind (λ a _, hob a)},
  { exact set.finite_univ }
end

noncomputable instance support.fintype [spec.finite_range] (oa : oracle_comp spec α) :
  fintype oa.support := (support_finite oa).fintype

/-- Since the range of oracles in an `oracle_spec` are required to be nonempty,
we naturally get that the `support` of an `oracle_comp` is nonempty. -/
theorem support_nonempty (oa : oracle_comp spec α) : oa.support.nonempty :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact set.singleton_nonempty a },
  { simp only [bind'_eq_bind, support_bind, set.nonempty_bUnion, exists_prop],
    exact let ⟨a, ha⟩ := hoa in ⟨a, ha, hob a⟩ },
  { simp only [support_query, set.top_eq_univ, set.univ_nonempty] }
end

/-- Should be able to automatically derive the support for most simple computations -/
example :
do{ β ← coin, β' ← coin,
    x ← if β then return 0 else return 1,
    y ← return (if β' then 1 else 0),
    z ← if β then return x else return (y - y),
    return (x * y * z) }.support = {0} := by simp

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

end oracle_comp