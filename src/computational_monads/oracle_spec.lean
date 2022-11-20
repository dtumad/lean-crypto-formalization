/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.fintype.basic

/-!
# Specification of Oracle Access

This file defines a type to represent the set of oracles available to a computation.
The `oracle_spec` type specifies an indexing set for the available oracles,
and input and output types for each oracle. We also require that the range of the oracle
is nonempty, so it has at least one possible output.

We also define type classes `computable` and `finite_range` for `oracle_spec`.
`computable` requires that we have `decidable_eq` instances on the involved types,
and `finite_range` requires that each oracle's output type is a `fintype`.
These will be used when defining `oracle_comp.fin_support` and `oracle_comp.eval_dist`.
-/

/-- Specification of the various oracles available to a computation.
`ι` is an indexing set of oracles (i.e. `ι := ℕ` gives a different oracle for each `n : ℕ`).
`domain range : ι → Type` give the input and output of the oracle corresponding to `i : ι`.
We also require for the output types to be nonempty (ensuring `oracle_comp.support` is nonempty) -/
structure oracle_spec : Type 1 := 
(ι : Type)
(domain range : ι → Type)
(range_inhabited (i : ι) : inhabited $ range i)

/-- Example of a simple `oracle_spec` for a pair of oracles,
  each taking a `ℕ` as input, returning a value of type `ℕ` or `ℤ` respectively -/
example : oracle_spec :=
{ ι := unit ⊕ unit,
  domain := λ _, ℕ,
  range := λ x, match x with | (sum.inl ()) := ℕ | (sum.inr ()) := ℤ end,
  range_inhabited := λ x, match x with
  | (sum.inl ()) := nat.inhabited
  | (sum.inr ()) := int.inhabited
  end }

namespace oracle_spec

section instances

instance range.inhabited {spec : oracle_spec} (i : spec.ι) : inhabited (spec.range i) :=
spec.range_inhabited i

variables (spec : oracle_spec)

/-- Class of `oracle_spec` that have decidable equality on the underlying types.
This is needed for things like cacheing previous queries or checking for specific queries.
It also allows for explicit calculation of the support of the computation (see `fin_support`)
We choose the name `computable` to avoid confusion with `oracle_comp.decidable` -/
class computable (spec : oracle_spec) :=
(ι_decidable_eq : decidable_eq spec.ι)
(domain_decidable_eq (i : spec.ι) : decidable_eq $ spec.domain i)
(range_decidable_eq (i : spec.ι) : decidable_eq $ spec.range i)

instance computable.ι_decidable_eq' [spec.computable] :
  decidable_eq spec.ι := computable.ι_decidable_eq

instance computable.domain_decidable_eq' [spec.computable] (i : spec.ι) :
  decidable_eq (spec.domain i) := computable.domain_decidable_eq i

instance computable.range_decidable_eq' [spec.computable] (i : spec.ι) :
  decidable_eq (spec.range i) := computable.range_decidable_eq i

/-- Class of `oracle_spec` for which the output type of each oracle has is a finite type.
In this case we can consider the distribution obtained by viewing each oracle as responding
uniformly at random (see `eval_dist` and `prob_event`) -/
class finite_range (spec : oracle_spec) :=
(range_fintype (i : spec.ι) : fintype $ spec.range i)

instance finite_range.range_fintype' [spec.finite_range] (i : spec.ι) :
  fintype (spec.range i) := finite_range.range_fintype i

end instances

section singleton_spec

/-- Access to a single oracle with input type `T` and output type `U`. -/
@[simps] def singleton_spec (T U : Type) [hU : inhabited U] : oracle_spec :=
{ ι := unit,
  domain := λ _, T,
  range := λ _, U,
  range_inhabited := λ _, hU }

infixl` ↦ₒ `:25 := singleton_spec

variables (T U : Type) [inhabited U]

instance singleton_spec.computable [hT : decidable_eq T] [hU' : decidable_eq U] :
  computable (T ↦ₒ U) :=
{ ι_decidable_eq := punit.decidable_eq,
  domain_decidable_eq := λ _, hT,
  range_decidable_eq := λ _, hU' }

instance singleton_spec.finite_range [hU : fintype U] : finite_range (T ↦ₒ U) :=
{ range_fintype := λ _, hU }

end singleton_spec

section empty_spec
 
/-- No access to any oracles. Represented by an empty indexing set via the `empty` type. -/
@[simps] def empty_spec : oracle_spec :=
{ ι := empty,
  domain := empty.elim,
  range := λ _, unit,
  range_inhabited := λ _, by apply_instance }

notation `[]ₒ` := empty_spec

instance empty_spec.computable : computable []ₒ := 
{ ι_decidable_eq := empty.decidable_eq,
  domain_decidable_eq := λ i, i.elim,
  range_decidable_eq := λ i, i.elim }

instance empty_spec.finite_range : finite_range []ₒ :=
{ range_fintype := λ i, i.elim }

end empty_spec

instance inhabited : inhabited oracle_spec := ⟨[]ₒ⟩

section append

/-- Combine two specifications using a `sum` type to index the different specs.
Given `spec spec' : oracle_spec`, `spec ++ spec'` gives access to the combined set of oracles,
with `sum.inl` corresponding to the left oracle and `sum.inr` corresponding to the right oracle. -/
instance oracle_spec.has_append : has_append oracle_spec :=
{ append := λ spec spec', 
  { ι := spec.ι ⊕ spec'.ι,
    domain := sum.elim spec.domain spec'.domain,
    range := sum.elim spec.range spec'.range,
    range_inhabited := λ i, by induction i; simp; apply_instance } }

variables (spec spec' : oracle_spec)

instance append.computable [spec.computable] [spec'.computable] :
  computable (spec ++ spec') :=
{ ι_decidable_eq := sum.decidable_eq spec.ι spec'.ι,
  domain_decidable_eq := by refine (λ i, sum.rec_on i _ _); exact computable.domain_decidable_eq,
  range_decidable_eq := by refine (λ i, sum.rec_on i _ _); exact computable.range_decidable_eq }

instance append.finite_range [spec.finite_range] [spec'.finite_range] :
  (spec ++ spec').finite_range :=
{ range_fintype := by refine (λ i, sum.rec_on i _ _); exact finite_range.range_fintype }

end append

section coin_spec

/-- Access to a single oracle, returning a `bool` to each oracle query.
The probability distribution associated to the oracle will eventually be 50/50 for `tt` and `ff`,
representing oracle access to a fair coin flip. -/
@[simps, derive [finite_range, computable]]
def coin_spec : oracle_spec := unit ↦ₒ bool

@[simp] lemma card_range_coin_spec (i : unit) : fintype.card (coin_spec.range i) = 2 := rfl

end coin_spec

section uniform_selecting

/-- Access to a `fin n` oracle for each `n : ℕ`, representing an oracle for evenly sampling
from a range of numbers. The output of the `n` query is actually in `fin (n + 1)`,
avoiding a return type of the empty `fin 0` type. -/
@[simps] def uniform_selecting : oracle_spec :=
{ ι := ℕ,
  domain := λ n, unit,
  range := λ n, fin (n + 1),
  range_inhabited := λ n, by apply_instance }

instance uniform_selecting.computable : computable uniform_selecting :=
{ ι_decidable_eq := nat.decidable_eq,
  domain_decidable_eq := λ _, by apply_instance,
  range_decidable_eq := λ n, fin.decidable_eq (n + 1) }

instance uniform_selecting.finite_range : finite_range uniform_selecting :=
{ range_fintype := λ n, fin.fintype (n + 1) }

@[simp] lemma card_range_uniform_selecting (n : ℕ) :
  fintype.card (uniform_selecting.range n) = n + 1 := finset.card_fin (n + 1)

end uniform_selecting

end oracle_spec 