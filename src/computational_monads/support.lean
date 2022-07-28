import set_theory.cardinal.basic

import computational_monads.oracle_comp

/-!
# Support of an Oracle Computation

This file defines two notions of the support of an `oracle_comp`

`support` returns a `set` of possible outputs of the computations,
  and is defined in general for any `oracle_comp`
`fin_support` instead returns a `finset`, but requires `decidable_eq` instances.

-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec} (a a' : α)
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)

section support

-- #check set.finite

/-- Set of possible outputs of the computation, allowing for any possible output of the queries.
  This will generally correspond to the support of `eval_distribution`,
    but is slightly more general since it doesn't require α finite range. -/
def support {spec : oracle_spec} : Π {α : Type} (oa : oracle_comp spec α), set α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := ⋃ α ∈ oa.support, (ob α).support
| _ (query i t) := ⊤

@[simp]
lemma support_pure (spec : oracle_spec) (a : α) :
  (pure a : oracle_comp spec α).support = {a} := rfl

@[simp]
lemma mem_support_pure_iff (a a' : α) :
  a' ∈ (pure a : oracle_comp spec α).support ↔ a' = a :=
set.mem_singleton_iff

lemma support_pure' (spec : oracle_spec) (a : α) :
  (pure' α a : oracle_comp spec α).support = {a} := rfl

lemma support_return (spec : oracle_spec) (a : α) :
  (return a : oracle_comp spec α).support = {a} := rfl

@[simp]
lemma support_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (oa >>= ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

@[simp]
lemma mem_support_bind_iff (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (β : β) :
  β ∈ (oa >>= ob).support ↔ ∃ α ∈ oa.support, β ∈ (ob α).support :=
by simp only [support_bind, set.mem_Union]

@[simp]
lemma support_query (i : spec.ι) (t : spec.domain i) :
  (query i t).support = ⊤ := rfl

@[simp]
lemma mem_support_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  u ∈ (query i t).support :=
set.mem_univ u

/-- If the range of `spec` is a `fintype` then the support is a finite set -/
theorem support_finite [h : ∀ i, fintype (spec.range i)]
  (oa : oracle_comp spec α) : oa.support.finite :=
begin
  induction oa with A a A B oa ob hoa hob i t,
  { simp },
  { simpa using set.finite.bind hoa (λ a _, hob a) },
  { simpa using set.finite_univ }
end

lemma support_bind' (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (bind' α β oa ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

@[simp]
lemma support_bind_bind (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) :
  (do {α ← oa, β ← ob α, oc α β}).support =
    ⋃ α ∈ oa.support, ⋃ β ∈ (ob α).support, (oc α β).support :=
by simp

@[simp]
lemma mem_support_bind_bind_iff (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) (c : γ) :
  c ∈ (do {α ← oa, β ← ob α, oc α β}).support ↔
    ∃ α ∈ oa.support, ∃ β ∈ (ob α).support, c ∈ (oc α β).support :=
by simp only [support_bind_bind, set.mem_Union]

@[simp]
lemma support_map (f : α → β) (oa : oracle_comp spec α) :
  (f <$> oa).support = f '' oa.support :=
calc (f <$> oa).support = ⋃ α ∈ oa.support, {f α} : rfl
  ... = f '' (⋃ α ∈ oa.support, {α}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

@[simp]
lemma mem_support_map_iff (f : α → β) (oa : oracle_comp spec α) (b : β) :
  b ∈ (f <$> oa).support ↔ ∃ a ∈ oa.support, f a = b :=
by simp only [support_map, set.mem_image, exists_prop]

example : support (do {
  β ← coin, β' ← coin,
  x ← if β then return 0 else return 1,
  y ← return (if β' then 1 else 0),
  return (x * y)
} : oracle_comp oracle_spec.coin_oracle ℕ) = {1, 0} :=
by simp

lemma support_pure_bind : (pure a >>= ob).support = (ob a).support :=
by simp

end support

section decidable

/-- Typeclass for computations that only return values of types with `decidable_eq` instances.
  In this case we can explicitly calculate the `support` as α `finset` rather than α `set`. -/
@[class]
inductive decidable {spec : oracle_spec} : 
  Π {α : Type}, oracle_comp spec α → Type 1
| decidable_pure' (α : Type) (a : α) (h : decidable_eq α) : decidable (pure' α a)
| decidable_bind' (α β : Type) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (hoa : decidable oa) (hob : ∀ α, decidable (ob α)) : decidable (bind' α β oa ob)
| decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t)

open decidable

def decidable.decidable_eq {spec : oracle_spec} [computable spec] :
  Π {α : Type} {oa : oracle_comp spec α}, decidable oa → decidable_eq α
| _ _ (decidable_pure' α a h) := h
| _ _ (decidable_bind' α β oa ob hoa hob) := let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq
| _ _ (decidable_query i t) := by apply_instance

section fin_support

/-- Compute an explicit `finset` of the elements in `support`. -/
def fin_support {spec : oracle_spec} [spec.computable] [spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α), decidable oa → finset α
| _ _ (decidable_pure' α a h) := {a}
| _ _ (decidable_bind' α β oa ob hoa hob) := 
  by haveI : decidable_eq β := (let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq);
  refine (fin_support oa hoa).bUnion (λ α, fin_support (ob α) (hob α))
| _ _ (decidable_query i t) := finset.univ

lemma mem_fin_support_iff_mem_support {spec : oracle_spec} [spec.computable] [spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α) (hoa : decidable oa) (α : α),
    α ∈ (fin_support oa hoa) ↔ α ∈ oa.support
| _ _ (decidable_pure' α a h) α' :=
    by simp [finset.coe_singleton α, support, fin_support]
| _ _ (decidable_bind' α β oa ob hoa hob) b :=
    by simp [fin_support, support, mem_fin_support_iff_mem_support]
| _ _ (decidable_query i t) u :=
    by simp [support, fin_support]

theorem coe_fin_support_eq_support {spec : oracle_spec} [spec.computable] [spec.finite_range]
  {α : Type} (oa : oracle_comp spec α) (hoa : decidable oa) :
    (fin_support oa hoa : set α) = oa.support :=
set.ext (mem_fin_support_iff_mem_support oa hoa)

end fin_support

end decidable


end oracle_comp