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

Note that we don't have a constructor for unbounded recursion such as a fixpoint.
This creates issues with the distributional semantics since without termination it may not exist.
In theory this could be solved by introducing a typeclass for finite computation,
and only defining distributions on computations with such an instance.
However without a clear use case, we avoid doing this for simplicity.
-/

variables {α β γ : Type} {spec spec' : oracle_spec}

open oracle_spec

/-- Type to represent computations with access so oracles specified by and `oracle_spec`. -/
inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| bind' (α β : Type) (oa : oracle_comp α) (ob : α → oracle_comp β) : oracle_comp β
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

namespace oracle_comp

instance nonempty (spec : oracle_spec) (α : Type) [h : nonempty α] :
  nonempty (oracle_comp spec α) := h.elim (λ x, ⟨pure' α x⟩)

instance inhabited (spec : oracle_spec) (α : Type) [h : inhabited α] :
  inhabited (oracle_comp spec α) := ⟨pure' α default⟩

/-- Simple computation for qurying a coin-flipping oracle for a single result. -/
@[reducible, inline] def coin : oracle_comp coin_spec bool := query () ()

section monad

/-- Natural monad structure on `oracle_comp`.
Simplification lemmas will tend towards `return` and `>>=` over `pure'` and `bind'`. -/
instance monad (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := oracle_comp.pure', bind := oracle_comp.bind' }

@[simp] lemma pure'_eq_return (spec) (a : α) :
  (pure' α a : oracle_comp spec α) = return a := rfl

@[simp] lemma pure_eq_return (spec) (a : α) :
  (pure a : oracle_comp spec α) = return a := rfl

@[simp] lemma bind'_eq_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  bind' α β oa ob = (oa >>= ob) := rfl

lemma map_eq_bind_return_comp (oa : oracle_comp spec α) (f : α → β) :
  f <$> oa = oa >>= return ∘ f := rfl

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

/-- Check that the induction principal works properly. -/
example (oa : oracle_comp spec α) : true := by induction oa using oracle_comp.induction_on; trivial

-- set_option eqn_compiler.lemmas false

/-- Given some computation `oa : oracle_comp spec α`, we can construct a "default" output `x : α`,
using the `default` value for each of the oracle output types (since they are `inhabited`). -/
def default_result {α : Type} (oa : oracle_comp spec α) : α :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact a },
  { exact hob hoa },
  { refine (spec.range_inhabited i).1 }
end

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type.
  The assumption that the range of the oracles is `inhabited` is the key point for this. -/
def base_inhabited (oa : oracle_comp spec α) : inhabited α := ⟨oa.default_result⟩

/-- Shorthand for querying the left side of two available oracles. -/
@[inline, reducible] def query₁ {spec spec' : oracle_spec}
  (i : spec.ι) (t : spec.domain i) : oracle_comp (spec ++ spec') (spec.range i) :=
@query (spec ++ spec') (sum.inl i) t

/-- Shorthand for querying the right side of two available oracles. -/
@[inline, reducible] def query₂ {spec spec' : oracle_spec}
  (i : spec'.ι) (t : spec'.domain i) : oracle_comp (spec ++ spec') (spec'.range i) :=
@query (spec ++ spec') (sum.inr i) t

end oracle_comp