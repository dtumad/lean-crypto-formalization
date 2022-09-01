import computational_monads.support

/-!
# Support of an Oracle Computation as a Finset

This file gives an alternative definition of the support of an `oracle_comp`.
Instead of a `set` as with `oracle_comp.support`, we introduce a definition
  `oracle_comp.fin_support` which gives the support as a `finset`.
The resulting `fin_set` is equal to `oracle_comp.support` when coerced to a `set`,
  see `fin_support_eq_support`.

This requires a number of decidability hypotheses for the computation itself.
To this end we introduce a type class `oracle_comp.decidable` for computations
  with decidable equality for any `return` type constructor.
The need for `decidable_eq` arises from the need to use `finset.bUnion` for the `bind` operation.

We also require a `computable` and `finite_range` instance for the `oracle_spec` itself.
Without the `finite_range` instance, the support may be infinite,
  so only `oracle_comp.support` will exist
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

section decidable

/-- Inductive def for computations that only return values of types with `decidable_eq` instances.
  In this case we can explicitly calculate the `support` as α `finset` rather than α `set`. -/
class inductive decidable : Π {α : Type}, oracle_comp spec α → Type 1
| decidable_pure' (α : Type) (a : α) (h : decidable_eq α) : decidable (pure' α a)
| decidable_bind' (α β : Type) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (hoa : decidable oa) (hob : ∀ α, decidable (ob α)) : decidable (bind' α β oa ob)
| decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t)

open decidable

variable [spec.computable]

/-- Version of `decidable_eq_of_decidable` taking an explicit `decidable` argument -/
def decidable_eq_of_decidable' : Π {α : Type} {oa : oracle_comp spec α}
  (h : decidable oa), decidable_eq α
| _ _ (decidable_pure' α a h) := h
| _ _ (decidable_bind' α β oa ob hoa hob) := decidable_eq_of_decidable' (hob (inhabited_base oa).1)
| _ _ (decidable_query i t) := oracle_spec.computable.range_decidable_eq i

/-- Given a `decidable` instance on an `oracle_comp`, we can extract a
  `decidable_eq` instance on the resutlt type of the computation -/
def decidable_eq_of_decidable (oa : oracle_comp spec α) [h : oa.decidable] :
  decidable_eq α := decidable_eq_of_decidable' h

variables [h : decidable_eq α] (a : α) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  [hoa : oa.decidable] [hob : ∀ a, (ob a).decidable]

instance decidable_return : decidable (return a : oracle_comp spec α) := decidable_pure' α a h

instance decidable_pure' : decidable (pure' α a : oracle_comp spec α) := decidable_pure' α a h

instance decidable_pure : decidable (pure a : oracle_comp spec α) := decidable_pure' α a h

instance decidable_bind : decidable (bind oa ob) := decidable_bind' α β oa ob hoa hob

instance decidable_bind' : decidable (bind' α β oa ob) := decidable_bind' α β oa ob hoa hob

instance decidable_map [h : decidable_eq β] (f : α → β) : decidable (f <$> oa) :=
decidable_bind' α β oa _ hoa (λ a, decidable_pure' β _ h)

instance decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t) :=
decidable_query i t

instance decidable_coin : decidable coin := decidable_query _ _

end decidable

/-- Simple computations should have automatic decidable instances -/
example : decidable (do {
  b ← coin, b' ← coin,
  x ← return (b && b'),
  y ← return (b || b'),
  return (if x then 1 else if y then 2 else 3)
}) := by apply_instance

section fin_support

open decidable

variables [h : spec.computable] [h' : spec.finite_range]
include h h'

/-- Version of `fin_support` taking an explicit `decidable` argument instead of an instance -/
def fin_support' : Π {α : Type} (oa : oracle_comp spec α), oa.decidable → finset α
| _ _ (decidable_pure' α a h) := {a}
| _ _ (decidable_bind' α β oa ob hoa hob) := 
  have hβ : decidable_eq β := decidable_eq_of_decidable' (hob $ (inhabited_base oa).1),
  @finset.bUnion α β hβ (fin_support' oa hoa) (λ a, fin_support' (ob a) (hob a))
| _ _ (decidable_query i t) := finset.univ

/-- Compute an explicit `finset` of the elements in `support`,
  assuming `computable` and `finite_range` instances on the `spec`,
  and a `decidable` instance on the `oracle_comp` itself. -/
def fin_support (oa : oracle_comp spec α) [hoa : oa.decidable] : finset α :=
oa.fin_support' hoa

lemma mem_fin_support'_iff_mem_support : Π {α : Type} (oa : oracle_comp spec α)
  (hoa : decidable oa) (a : α), a ∈ (fin_support' oa hoa) ↔ a ∈ oa.support
| _ _ (decidable_pure' α a h) α' :=
    by simp [finset.coe_singleton α, support, fin_support']
| _ _ (decidable_bind' α β oa ob hoa hob) b :=
    by simp [fin_support', support, mem_fin_support'_iff_mem_support]
| _ _ (decidable_query i t) u :=
    by simp [support, fin_support']

lemma mem_fin_support_iff_mem_support (oa : oracle_comp spec α) [hoa : oa.decidable]
  (a : α) : a ∈ oa.fin_support ↔ a ∈ oa.support :=
mem_fin_support'_iff_mem_support oa hoa a

/-- Correctness of `fin_support` with respect to `support`, i.e. the two are equal as `set`s -/
theorem support_eq_fin_support (oa : oracle_comp spec α) [oa.decidable] :
  oa.support = oa.fin_support :=
set.ext (λ a, (mem_fin_support_iff_mem_support oa a).symm)

lemma support_subset_fin_support (oa : oracle_comp spec α) [decidable oa] :
  oa.support ⊆ oa.fin_support :=
by rw [support_eq_fin_support oa]

lemma fin_support_subset_support (oa : oracle_comp spec α) [decidable oa] :
  ↑oa.fin_support ⊆ oa.support :=
by rw [support_eq_fin_support oa]

end fin_support

end oracle_comp