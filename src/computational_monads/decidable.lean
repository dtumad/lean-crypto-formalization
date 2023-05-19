/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_comp

/-!
# Decidable Computations

This file defines a typeclass `oracle_comp.decidable` for computations that have `decidable_eq`
instances for every return value in the computation.
We don't currently make use of this very much in general, becuase `open_locale classical` makes
it unnecessary, but if this eventually gets removed then things like `oracle_comp.fin_support`
will require it to function
-/

namespace oracle_comp

variables {α β : Type} {spec : oracle_spec}

/-- Inductive definition for computations that only return values of types with `decidable_eq`.
In this case we can explicitly calculate the `support` as a `finset` rather than a `set`.
TODO: this seems like bad naming? overlaps? `decidable_comp`? -/
class inductive decidable : Π {α : Type}, oracle_comp spec α → Type 1
| decidable_pure' (α : Type) (a : α) (h : decidable_eq α) : decidable (pure' α a)
| decidable_bind' (α β : Type) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (hoa : decidable oa) (hob : ∀ α, decidable (ob α)) : decidable (bind' α β oa ob)
| decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t)

open decidable

/-- Version of `decidable_eq_of_decidable` taking an explicit `decidable` argument -/
def decidable_eq_of_decidable' : Π {α : Type} {oa : oracle_comp spec α}
  (h : decidable oa), decidable_eq α
| _ _ (decidable_pure' α a h) := h
| _ _ (decidable_bind' α β oa ob hoa hob) := decidable_eq_of_decidable' (hob (base_inhabited oa).1)
| _ _ (decidable_query i t) := spec.range_decidable_eq i

/-- Given a `decidable` instance on an `oracle_comp`, we can extract a
  `decidable_eq` instance on the resutlt type of the computation -/
def decidable_eq_of_decidable (oa : oracle_comp spec α) [h : oa.decidable] :
  decidable_eq α := decidable_eq_of_decidable' h

instance decidable_return [h : decidable_eq α] (a : α) :
  decidable (return a : oracle_comp spec α) := decidable_pure' α a h

instance decidable_pure' [h : decidable_eq α] (a : α) :
  decidable (pure' α a : oracle_comp spec α) := decidable_pure' α a h

instance decidable_pure [h : decidable_eq α] (a : α) :
  decidable (pure a : oracle_comp spec α) := decidable_pure' α a h

instance decidable_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) [h : decidable oa]
  [h' : ∀ a, decidable (ob a)] : decidable (oa >>= ob) := decidable_bind' α β oa ob h h'

instance decidable_bind' (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) [h : decidable oa]
  [h' : ∀ a, decidable (ob a)] : decidable (bind' α β oa ob) := decidable_bind' α β oa ob h h'

instance decidable_map [h : decidable_eq β] (oa : oracle_comp spec α) [h' : oa.decidable]
  (f : α → β) : decidable (f <$> oa) := decidable_bind' α β oa _ h' (λ a, decidable_pure' β _ h)

instance decidable_query (i : spec.ι) (t : spec.domain i) :
  decidable (query i t) := decidable_query i t

instance decidable_coin : decidable coin := decidable_query _ _

def decidable_of_decidable_bind_fst {oa : oracle_comp spec α} {ob : α → oracle_comp spec β} :
  Π (h : decidable (oa >>= ob)), oa.decidable
| (decidable_bind' α β _ _ hoa hob) := hoa

def decidable_of_decidable_bind_snd {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  (a : α) : Π (h : decidable (oa >>= ob)), (ob a).decidable
| (decidable_bind' α β _ _ hoa hob) := hob a

/-- Simple computations should have automatic decidable instances -/
example :
do {b ← coin, b' ← coin,
    x ← return (b && b'),
    y ← return (b || b'),
    return (if x then 1 else if y then 2 else 3)}.decidable := by apply_instance

end oracle_comp