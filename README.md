# FCF implementation in Lean

This repo contains an implementation of FCF as specified [here](https://dash.harvard.edu/bitstream/handle/1/17463136/PETCHER-DISSERTATION-2015.pdf) in Lean.
The implementation makes a number of changes and generalizations to the original system, most significantly in the computational monads and representation of oracle access.
It also makes use of the features of Lean itself to simplify the process of specifying and reasoning about cryptographic constructions,
and focuses on tight integration with the mathlib project to provide a good API for handling the mathematical reasoning involved in cryptography.

## Oracle Access and Probabilistic Computation

`src/computational_monads` contains the definition of the main computational monad, `oracle_comp`.
This definition generalizes both the `oracle_comp` and `prob_comp` monads of FCF, allowing for a computation with a indexed set of oracles.
This also allows for an infinite set of oracles (for example ring signature signing oracles indexed by the number of signers for the signature).

`src/computational_monads/simulation_semantics` defines a way to reduce a computation with access to some set of oracles to one with access to a different set of oracles by specifying how to evaluate the old oracle calls with the new set of oracles (potentially using some kind of persistent state across oracle calls)
It also contains basic constructions of oracles, including logging oracles, random oracles, and ways to combine and compose oracles to construct more complex oracles.
Simulation semantics are also used to define a number of coercions between computations with less oracles to more oracles in order to simplify the specification of algorithms and oracles.

`src/computational_monads/distribution_semantics` defines a denotational semantics for computations with access to simple oracles, such as a coin oracle or uniform selection oracle.
The denotation is given by a probability mass function, using the `pmf` definition in mathlib.
It also defines the notion of computations being equivalent under the distribution semantics, and the probability of an event holding after a computation (as a specialization of the outer measure associated to the probability distribution).

The general structure of most constructions is to first use the simulation semantics to reduce a computation to a simple set of basic oracles, and then to use the distribution semantics to reason about the corresponding probability distribution for the computation.

`src/computational_monads/asymptotics` defines notions of polynomial complexity and polynomial queries for these computations.
It also defines the notion of a negligible function (as a special definition of mathlib's `superpolynomial_decay`)

## Cryptographic Constructions

`src/crypto_foundations` contains the basic definitions of many cryptographic objects, including hardness assumptions like Diffie-Hellman (in terms of the more general notion of a hard homogenous spaces), as well as objects like hash functions and (ring)signature schemes.

`src/crypto_constructions` defines particular implementations of the objects, such as a specific signature scheme.