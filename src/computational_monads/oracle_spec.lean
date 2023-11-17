/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.fintype.card

/-!
# Specification of Oracle Access For a Computation

This file defines a type to represent the set of oracles available to a computation.
The `oracle_spec` type specifies an indexing set for the available oracles,
and input and output types for each oracle. We also require that the range of the oracle
is nonempty so it has at least one possible output, and that the range of the oracle
is finite so that each *particular* oracle has a finite number of outputs.

We choose to include `decidable_eq` assumptions for the types in the structure rather than
as further typeclasses on `oracle_spec` for simplicity, but generally these could be seperated.

We also define a number of basic constructions for common oracles:
- `singleton_spec` represents a single oracle with a specified input and output type (`T →ₒ U`).
- `empty_spec` represents a lack of any oracles (represented as `∅`).
- `append` represents bringing together two sets of oracles into one combined set of oracles.
- `coin_spec` represents access to a coin flipping oracle
- `uniform_selecting` represents access to a uniformly random oracle on a numeric range.
-/

/-- Specification of the various oracles available to a computation.
`ι` is an indexing set of oracles (i.e. `ι := ℕ` gives a different oracle for each `n : ℕ`).
`domain range : ι → Type` give the input and output types of the oracle corresponding to an index.
We also require for the output types to be nonempty (ensuring `oracle_comp.support` is nonempty).
`decidable_eq` and `fintype` instances are also required for each oracle index, in order
to define things like `fin_support`. Note that this is only required *per index*, the
total number of oracle outputs may be infinite, it must only be finite for any *specific* index. -/
structure oracle_spec :=
(ι : Type)
(domain range : ι → Type)
-- Type class instances. These could eventually be seperated for more generality.
(ι_decidable_eq : decidable_eq ι)
(domain_decidable_eq : ∀ i, decidable_eq $ domain i)
(range_decidable_eq : ∀ i, decidable_eq $ range i)
(range_inhabited : ∀ i, inhabited $ range i)
(range_fintype : ∀ i, fintype $ range i)

namespace oracle_spec

instance ι.decidable_eq' (spec : oracle_spec) : decidable_eq spec.ι := spec.ι_decidable_eq

instance domain.decidable_eq' {spec : oracle_spec} (i : spec.ι) :
  decidable_eq (spec.domain i) := spec.domain_decidable_eq i

instance range.decidable_eq' {spec : oracle_spec} (i : spec.ι) :
  decidable_eq (spec.range i) := spec.range_decidable_eq i

instance range.inhabited {spec : oracle_spec} (i : spec.ι) :
  inhabited (spec.range i) := spec.range_inhabited i

instance range.fintype' {spec : oracle_spec} (i : spec.ι) :
  fintype (spec.range i) := spec.range_fintype i

@[simp] lemma card_range_ne_zero {spec : oracle_spec} (i : spec.ι) :
  fintype.card (spec.range i) ≠ 0 := fintype.card_ne_zero

/-- No access to any oracles. Represented by an empty indexing set via the `empty` type.
Since `empty` is uninhabited, it isn't possible to construct a query to this oracle.
We use `unit` for the input and output types but this is just a dummy value. -/
@[simps] def empty_spec : oracle_spec :=
{ ι := empty,
  domain := λ _, unit,
  range := λ _, unit,
  range_inhabited := λ _, infer_instance,
  ι_decidable_eq := empty.decidable_eq,
  domain_decidable_eq := λ i, i.elim,
  range_decidable_eq := λ i, i.elim,
  range_fintype := λ i, i.elim }

instance : is_empty empty_spec.ι := empty.is_empty
instance (i : empty_spec.ι) : unique (empty_spec.domain i) := punit.unique
instance (i : empty_spec.ι) : unique (empty_spec.range i) := punit.unique

instance : has_emptyc oracle_spec := ⟨empty_spec⟩
instance inhabited : inhabited oracle_spec := ⟨∅⟩

/-- `oracle_spec` representing access to a single oracle with input type `T` and output type `U`.
We use the `unit` type as the index since there is exactly one unique oracle available. -/
@[simps] def singleton_spec (T U : Type) [hU : inhabited U] [hT : decidable_eq T]
  [hU' : decidable_eq U] [hU'' : fintype U] : oracle_spec :=
{ ι := unit,
  domain := λ _, T,
  range := λ _, U,
  range_inhabited := λ _, hU,
  ι_decidable_eq := punit.decidable_eq,
  domain_decidable_eq := λ _, hT,
  range_decidable_eq := λ _, hU',
  range_fintype := λ _, hU'' }

infixl` ↦ₒ `:25 := singleton_spec

instance singleton_spec_ι_unique (T U : Type) [inhabited U] [decidable_eq T] [decidable_eq U]
  [fintype U] : unique (T ↦ₒ U).ι := punit.unique

/-- Combine two specifications using a `sum` type to index the different specs.
Given `spec spec' : oracle_spec`, `spec ++ spec'` gives access to the combined set of oracles,
with `sum.inl` corresponding to the left oracle and `sum.inr` corresponding to the right oracle. -/
instance has_append : has_append oracle_spec :=
{ append := λ spec spec',
  { ι := spec.ι ⊕ spec'.ι,
    domain := sum.elim spec.domain spec'.domain,
    range := sum.elim spec.range spec'.range,
    range_inhabited := λ i, by induction i; simp; apply_instance,
    ι_decidable_eq := sum.decidable_eq spec.ι spec'.ι,
    domain_decidable_eq := λ i, sum.rec_on i spec.domain_decidable_eq spec'.domain_decidable_eq,
    range_decidable_eq := λ i, sum.rec_on i spec.range_decidable_eq spec'.range_decidable_eq,
    range_fintype := λ i, sum.rec_on i spec.range_fintype spec'.range_fintype } }

@[simp] lemma append.domain_inl (spec spec' : oracle_spec) (i : spec.ι) :
  (spec ++ spec').domain (sum.inl i) = spec.domain i := rfl

@[simp] lemma append.domain_inr (spec spec' : oracle_spec) (i : spec'.ι) :
  (spec ++ spec').domain (sum.inr i) = spec'.domain i := rfl

@[simp] lemma append.range_inl (spec spec' : oracle_spec) (i : spec.ι) :
  (spec ++ spec').range (sum.inl i) = spec.range i := rfl

@[simp] lemma append.range_inr (spec spec' : oracle_spec) (i : spec'.ι) :
  (spec ++ spec').range (sum.inr i) = spec'.range i := rfl

/-- Access to a single oracle, returning a `bool` to each oracle query.
The probability distribution associated to the oracle will eventually be 50/50 for `tt` and `ff`,
representing oracle access to a fair coin flip. -/
@[simps] def coin_spec : oracle_spec := unit ↦ₒ bool

@[simp] lemma card_range_coin_spec (i : unit) : fintype.card (coin_spec.range i) = 2 := rfl

/-- Access to a `fin n` oracle for each `n : ℕ`, representing an oracle for evenly sampling
from a range of numbers. The output of the `n` query is actually in `fin (n + 1)`,
avoiding a return type of the empty `fin 0` type. -/
@[simps] def uniform_selecting : oracle_spec :=
{ ι := ℕ,
  domain := λ n, unit,
  range := λ n, fin (n + 1),
  range_inhabited := λ n, ⟨0⟩,
  ι_decidable_eq := nat.decidable_eq,
  domain_decidable_eq := λ _, punit.decidable_eq,
  range_decidable_eq := λ n, fin.decidable_eq (n + 1),
  range_fintype := λ n, fin.fintype (n + 1) }

@[simp] lemma card_range_uniform_selecting (n : ℕ) :
  fintype.card (uniform_selecting.range n) = n + 1 := finset.card_fin (n + 1)

/-- Example of an `oracle_spec` for a pair of oracles each taking a natural `n : ℕ` as input,
returning a value of type `fin 100` or `bool` respectively, using a sum type for indexing.
In practice the instances like `range_inhabited` will usually be derived automatically,
but we expand them here to show the explicit definitions.  -/
example : oracle_spec :=
{ ι := unit ⊕ unit,
  domain := λ _, ℕ,
  range := λ x, match x with | (sum.inl ()) := fin 100 | (sum.inr ()) := bool end,
  range_inhabited := λ x, match x with
  | (sum.inl ()) := fin.inhabited
  | (sum.inr ()) := bool.inhabited
  end,
  ι_decidable_eq := sum.decidable_eq unit unit,
  domain_decidable_eq := λ _, nat.decidable_eq,
  range_decidable_eq := λ x, match x with
  | (sum.inl ()) := fin.decidable_eq 100
  | (sum.inr ()) := bool.decidable_eq
  end,
  range_fintype := λ x, match x with
  | (sum.inl ()) := fin.fintype 100
  | (sum.inr ()) := bool.fintype
  end }

end oracle_spec