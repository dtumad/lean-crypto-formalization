# FCF implementation in Lean

This repo contains a partial implementation of FCF as specified [here](https://dash.harvard.edu/bitstream/handle/1/17463136/PETCHER-DISSERTATION-2015.pdf).

`src/crypto_foundations/comp.lean` and `src/crypto_foundations/dist_sem.lean` contain a model for nondeterministic computations and the semantics of these computations respectively.

`src/computational_complexity` contains definitions for specifying runtime costs of algorithms, and for proving asymptotic facts about these runtimes.

`src/crypto_foundations/hardness_assumptions` contains hardness definitions for Diffie-Hellman and Hard Homogenous Spaces

`src/crypto_foundations/primitives/ring_signatures` contains partial work on defining and proving the security of a ring signature scheme based on Hard Homogenous Spaces.
