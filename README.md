# VCV-io: Formal Verification of Cryptography Proofs in Lean

This library provides a framework for verifying security proofs of cryptographic protocols, taking a foundational approach to representing different protocols and computation.
The system makes use of the Lean proof assistant, and gives constructions to represent and reason about computations with various oracles.
It provides semantics both for calculating probabilities and for simulating oracles in a stateful way.
Mathematical foundations are built from or contributed to the open-source Mathlib project whenever possible.

TODO/NOTE: this needs to be updated with the recent changes to simulation semantics and tactic programming.

## Representing Non-Deterministic Computations and Oracles

`src/computational_monads` contains the definition of the main computational monad `oracle_comp`, as well as it's semantics and various constructions of computations.
This monad is used to augment Lean functions with a single additional operation, namely oracle queries to one of a set of available oracles.

The set of oracles available to such a computation is are specified by a `oracle_spec` structure, that gives a set of oracles that the computation may call, parameterized by some indexing set.
Non-deterministic computation is defined as the special case of having access to a coin-flip oracle.
A number of common oracle sets are pre-defined in the library, including:
* `coin_spec` is a single oracle for flipping a coin.
* `T ↦ₒ U` is a single oracle with input type `T` and output type `U`.
* `∅` gives access to no oracles at all.
* `spec₁ ++ spec₂` has access to all oracles of the two given oracle sets.

Given some `spec : oracle_spec` and `α : Type`, `oracle_comp spec α` is the type of computations with the oracles given in `spec` and a final output of type `α`.
The definition is given by three inductive type constructors:
* `return a` returns the given value `a`.
* `oa >>= ob` runs `oa` to get a value `x`, then runs `ob x`.
* `query i t` queries the oracle corresponding to index `i` with input `t`

A number of common computations are built from these basic pieces:
* `repeat oa n` runs `oa` multiple times in parallel and returns all the results.
* `try_until p oa n` runs repeatedly runs `oa` until `p` holds, failing after `n` attempts.
* `flip_coin` flips a fair coin.
* `$[0..n]` chooses a value between `0` and `n` uniformly at random.
* `$ᵗ α` chooses an element from `α` uniformly at random.
* `fork oa choose_fork` runs `oa`, rewinds to a point determined post-hoc by `choose_fork`, and returns both the original and new result of the two runs.

Lean's built in `do` notation can also be used to specify computations:
```
do { n ← $[0..n],
     b ← flip_coin,
     return (if b then n else 0) }
```

## Simulating Oracle Queries

`src/computational_monads/simulation_semantics` defines a way to reduce a computation with access to some set of oracles to one with access to a different set of oracles by specifying how to evaluate the old oracle queries with the new set of oracles (potentially using some kind of persistent state across oracle calls).
The simulation method is given by a structure `so : sim_oracle spec₁ spec₂ S`
It also defines a number of simulation oracles for common functionalities:
* `logging_oracle` augments the computation with a log of all queries to oracles.
* `random_oracle` answers new queries at random and caches the result for any further queries.
* `seeded_oracle` takes a preset cache of responses to use in query responses.
* `so₁ ++ so₂` combines two oracles for simulating two subsets of the oracle queries.

These semantics are also used to define automatic coercions between computations with some set of oracles to one with some super-set of oracles.
This allows computations with a limited set of oracles to be re-used in other setting, and reductions back down to the original computation are handled by the `simp` tactic.

## Calculating Output Probabilities

`src/computational_monads/distribution_semantics` defines a denotational semantics `eval_dist` for computations with access to simple oracles, such as a coin oracle or uniform selection oracle.
The denotation is given by a probability mass function, using the `pmf` type from mathlib.
It also defines the probability of an event holding after a computation `prob_event` as a specialization of the outer measure associated to the probability distribution.
A number of notations are defined to simplify writing probability proofs:
* `oa.support` is the set of outputs of `oa` with non-zero probability of being returned.
* `⁅oa⁆` is the probability distribution associated to `oa`.
* `⁅= x | oa⁆` is the probability the `x` is returned by `oa`.
* `⁅e | oa⁆` is the probability that the result of running `oa` is in the event `e`.

We can characterize these definitions based on their results on the three basic computations:
```
(return x).support := {x}
⁅= y | return x⁆ := if y = x then 1 else 0
⁅e | return x⁆ := if x ∈ e then 1 else 0
```
```
(oa >>= ob).support := ⋃ x ∈ oa.support, (ob x).support
⁅= y | oa >>= ob⁆ := ∑' x, ⁅= x | oa⁆ * ⁅= y | ob x⁆
⁅e | oa >>= ob⁆ := ∑' x, ⁅= x | oa⁆ * ⁅ e | ob x⁆
```
```
(query i t).support := set.univ
⁅= u | query i t⁆ := 1 / (spec.range i).card
⁅e | query i t⁆ := e.card / (spec.range i).card
```

## Asymptotics

`src/computational_monads/asymptotics` contains three main asymptotic definitions common in cryptographic proofs:
* `polynomial_time` extends mathlib's `tm2_computable_in_poly_time` (based on Turing machines) to the `oracle_comp` monad to define polynomial time computations.
* `negligible` is a standard definition of negligible functions, as a specialization of mathlib's `superpolynomial_decay`.
* `queries_at_most` gives a way to bound the number of queries made by a given computation, and to in particular bound it by a polynomial.

## Cryptographic Constructions

`src/crypto_foundations` contains the basic definitions of many cryptographic objects, including hardness assumptions like Diffie-Hellman (in terms of the more general notion of a hard homogenous spaces), as well as objects like hash functions and (ring)signature schemes.

`src/crypto_constructions` contains examples of protocols and security proofs, including an unforgeability proof of a Schnorr signature scheme based on hard homogenous spaces.

## General Math Lemmas

`src/to_mathlib` contains general mathematical lemmas that can apply more generally than in the project (such as lemmas about `tsum`, `list`, or `pmf`)