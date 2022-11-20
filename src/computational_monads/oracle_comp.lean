/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec

/-!
# Computations with Oracle Access

This file defines a representation of a computation with access to a set of oracles,
given by some `oracle_spec`. `oracle_comp spec α` will represent a computation
using the oracles of `spec : oracle_spec`, returning values of type `α`.
The definion is similar to a free monad, having built in `bind` and `pure` operations,
and an additional constructor for oracle queries.

We give probability distribution semantics for such a computation as `eval_dist` and `prob_event`.
`simulate` and `simulate'` will give semantics for running a computation by simulating the
oracles, using a (potentially empty) different set of oracles.

Notationally, we tend towards using `return` and `>>=` for the monadic operations,
and do-notation for specifying longer computations.

We additionally define a `decidable` typeclass for computations for which return values
all have `decidable_eq` instances, which will later be used to define `fin_support`.
-/

variables {α β γ : Type} {spec spec' : oracle_spec}

open oracle_spec

/-- Type to represent computations with access so oracles specified by and `oracle_spec`. -/
inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| bind' (α β : Type) (oa : oracle_comp α) (ob : α → oracle_comp β) : oracle_comp β
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

namespace oracle_comp

/-- Simple computation for qurying a coin-flipping oracle for a single result. -/
@[reducible, inline] def coin : oracle_comp coin_spec bool := query () ()

section monad

/-- Natural monad structure on `oracle_comp`.
Simplification lemmas will tend towards `return` and `>>=` over `pure'` and `bind'`. -/
instance monad (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := oracle_comp.pure', bind := oracle_comp.bind' }

@[simp] lemma pure'_eq_return (spec : oracle_spec) (a : α) :
  (pure' α a : oracle_comp spec α) = return a := rfl

@[simp] lemma pure_eq_return (spec : oracle_spec) (a : α) :
  (pure a : oracle_comp spec α) = return a := rfl

@[simp] lemma bind'_eq_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  bind' α β oa ob = (oa >>= ob) := rfl

lemma map_eq_bind (oa : oracle_comp spec α) (f : α → β) : f <$> oa = oa >>= return ∘ f := rfl

/-- Simple computation flipping two coins and returning a value based on them -/
example : oracle_comp coin_spec ℕ :=
do { b ← coin, b' ← coin,
  x ← return (if b && b' then 2 else 3),
  y ← return (if b || b' then 3 else 4),
  return (x * y) }

end monad

/-- Slightly nicer induction priciple, avoiding use of `bind'` and `pure'`.
  Use as induction principle with `induction oa using oracle_comp.induction_on` -/
@[elab_as_eliminator] def induction_on {C : Π {α : Type}, oracle_comp spec α → Sort*}
  {α : Type} (oa : oracle_comp spec α)
  (h_return : ∀ {α : Type} (a : α), C (return a))
  (h_bind : ∀ {α β : Type} {oa : oracle_comp spec α} {ob : α → oracle_comp spec β},
    C oa → (∀ a, C (ob a)) → C (oa >>= ob) )
  (h_query : ∀ i t, C (query i t)) : C oa :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact h_return _ },
  { exact h_bind hoa hob },
  { exact h_query i t }
end

/-- Check that the induction principal works properly -/
example (oa : oracle_comp spec α) : true := by induction oa using oracle_comp.induction_on; trivial

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type.
  The assumption that the range of the oracles is `inhabited` is the key point for this -/
def inhabited_base (oa : oracle_comp spec α) : inhabited α :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact ⟨a⟩ },
  { exact let ⟨a⟩ := hoa in hob a },
  { exact ⟨arbitrary (spec.range i)⟩ }
end

/-- Shorthand for querying the left side of two available oracles -/
@[inline, reducible] def query₁ {spec spec' : oracle_spec}
  (i : spec.ι) (t : spec.domain i) : oracle_comp (spec ++ spec') (spec.range i) :=
@query (spec ++ spec') (sum.inl i) t

/-- Shorthand for querying the right side of two available oracles -/
@[inline, reducible] def query₂ {spec spec' : oracle_spec}
  (i : spec'.ι) (t : spec'.domain i) : oracle_comp (spec ++ spec') (spec'.range i) :=
@query (spec ++ spec') (sum.inr i) t

section decidable

/-- Inductive definition for computations that only return values of types
with `decidable_eq` instances. In this case we can explicitly calculate the `support`
as a `finset` rather than a `set`. -/
class inductive decidable : Π {α : Type}, oracle_comp spec α → Type 1
| decidable_pure' (α : Type) (a : α) (h : decidable_eq α) : decidable (pure' α a)
| decidable_bind' (α β : Type) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (hoa : decidable oa) (hob : ∀ α, decidable (ob α)) : decidable (bind' α β oa ob)
| decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t)

open decidable

/-- Version of `decidable_eq_of_decidable` taking an explicit `decidable` argument -/
def decidable_eq_of_decidable' [spec.computable] : Π {α : Type} {oa : oracle_comp spec α}
  (h : decidable oa), decidable_eq α
| _ _ (decidable_pure' α a h) := h
| _ _ (decidable_bind' α β oa ob hoa hob) := decidable_eq_of_decidable' (hob (inhabited_base oa).1)
| _ _ (decidable_query i t) := oracle_spec.computable.range_decidable_eq i

/-- Given a `decidable` instance on an `oracle_comp`, we can extract a
  `decidable_eq` instance on the resutlt type of the computation -/
def decidable_eq_of_decidable [spec.computable] (oa : oracle_comp spec α) [h : oa.decidable] :
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

def decidable_of_decidable_bind_fst {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  : Π (h : decidable (oa >>= ob)), oa.decidable
| (decidable_bind' α β _ _ hoa hob) := hoa

def decidable_of_decidable_bind_snd {oa : oracle_comp spec α} {ob : α → oracle_comp spec β} (a : α)
  : Π (h : decidable (oa >>= ob)), (ob a).decidable
| (decidable_bind' α β _ _ hoa hob) := hob a

end decidable

/-- Simple computations should have automatic decidable instances -/
example : decidable (do {
  b ← coin, b' ← coin,
  x ← return (b && b'),
  y ← return (b || b'),
  return (if x then 1 else if y then 2 else 3)
}) := by apply_instance

end oracle_comp