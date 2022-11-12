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
This aligns with `pmf.support` for the distribution semantics of `oracle_comp.eval_dist`
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Set of possible outputs of the computation, allowing for any possible output of the queries.
  This will generally correspond to the support of `eval_dist`,
    but is slightly more general since it doesn't require α finite range. -/
def support {spec : oracle_spec} : Π {α : Type} (oa : oracle_comp spec α), set α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := ⋃ α ∈ oa.support, (ob α).support
| _ (query i t) := ⊤

section return

@[simp] lemma support_return (spec : oracle_spec) (a : α) :
  (return a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_return_iff (spec : oracle_spec) (a a' : α) :
  a' ∈ (return a : oracle_comp spec α).support ↔ a' = a := set.mem_singleton_iff

lemma support_pure' (spec : oracle_spec) (a : α) :
  (pure' α a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_pure'_iff (spec : oracle_spec) (a a' : α) :
  a' ∈ (pure' α a : oracle_comp spec α).support ↔ a' = a := set.mem_singleton_iff

lemma support_pure (spec : oracle_spec) (a : α) :
  (pure a : oracle_comp spec α).support = {a} := rfl

lemma mem_support_pure_iff (a a' : α) :
  a' ∈ (pure a : oracle_comp spec α).support ↔ a' = a := set.mem_singleton_iff

end return

section bind 

@[simp] lemma support_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (oa >>= ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

lemma mem_support_bind_iff (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (β : β) :
  β ∈ (oa >>= ob).support ↔ ∃ α ∈ oa.support, β ∈ (ob α).support :=
by simp only [support_bind, set.mem_Union]

lemma support_bind' (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (bind' α β oa ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

lemma mem_support_bind'_iff (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (b : β) :
  b ∈ (bind' α β oa ob).support ↔ ∃ a ∈ oa.support, b ∈ (ob a).support :=
by simp only [bind'_eq_bind, support_bind, set.mem_Union]

lemma support_bind_bind (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) :
  (do {α ← oa, β ← ob α, oc α β}).support =
    ⋃ α ∈ oa.support, ⋃ β ∈ (ob α).support, (oc α β).support :=
by simp only [support_bind]

lemma mem_support_bind_bind_iff (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) (c : γ) :
  c ∈ (do {a ← oa, b ← ob a, oc a b}).support ↔
    ∃ a ∈ oa.support, ∃ b ∈ (ob a).support, c ∈ (oc a b).support :=
by simp only [support_bind_bind, set.mem_Union]

lemma support_return_bind (a : α) (ob : α → oracle_comp spec β) :
  (return a >>= ob).support = (ob a).support :=
by simp only [support_bind, mem_support_pure_iff, set.Union_Union_eq_left]

lemma mem_support_return_bind_iff (a : α) (ob : α → oracle_comp spec β) (b : β) :
  b ∈ (return a >>= ob).support ↔ b ∈ (ob a).support :=
by simp only [support_bind, mem_support_pure_iff, set.Union_Union_eq_left]

@[simp] lemma support_bind_return (oa : oracle_comp spec α) (f : α → β) :
  (oa >>= λ a, return (f a)).support = f '' oa.support :=
calc (f <$> oa).support = ⋃ α ∈ oa.support, {f α} : rfl
  ... = f '' (⋃ α ∈ oa.support, {α}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

lemma mem_support_bind_return (oa : oracle_comp spec α) (f : α → β) (b : β) :
  b ∈ (oa >>= λ a, return (f a)).support ↔ ∃ a ∈ oa.support, f a = b :=
by simp only [support_bind_return, set.mem_image, exists_prop]

end bind

section query

@[simp] lemma support_query (i : spec.ι) (t : spec.domain i) :
  (query i t).support = ⊤ := rfl

lemma mem_support_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  u ∈ (query i t).support := set.mem_univ u

end query

/-- If the range of `spec` is a `fintype` then the support is a finite set -/
theorem support_finite [spec.finite_range] (oa : oracle_comp spec α) : oa.support.finite :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact set.finite_singleton a },
  { exact hoa.bind (λ a _, hob a)},
  { exact set.finite_univ }
end

noncomputable instance support.fintype [spec.finite_range] (oa : oracle_comp spec α) :
  fintype oa.support := (support_finite oa).fintype

theorem support_nonempty (oa : oracle_comp spec α) : oa.support.nonempty :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact set.singleton_nonempty a },
  { simp only [bind'_eq_bind, support_bind, set.nonempty_bUnion, exists_prop],
    exact let ⟨a, ha⟩ := hoa in ⟨a, ha, hob a⟩ },
  { simp only [support_query, set.top_eq_univ, set.univ_nonempty] }
end

section map

@[simp] lemma support_map (f : α → β) (oa : oracle_comp spec α) :
  (f <$> oa).support = f '' oa.support := support_bind_return oa f

lemma mem_support_map_iff (f : α → β) (oa : oracle_comp spec α) (b : β) :
  b ∈ (f <$> oa).support ↔ ∃ a ∈ oa.support, f a = b := mem_support_bind_return oa f b

end map

/-- Should be able to automatically derive the support for most simple computations -/
example : do {
  β ← coin, β' ← coin,
  x ← if β then return 0 else return 1,
  y ← return (if β' then 1 else 0),
  return (x * y)
}.support = {1, 0} := by simp

example : do {
  β ← coin,
  x ← return (if β then 1 else 0),
  y ← return (if β then 0 else 1),
  return (x * y)
}.support = {0} := by simp

end oracle_comp