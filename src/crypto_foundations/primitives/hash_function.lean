/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.prob_event
import computational_monads.asymptotics.polynomial_time
import computational_monads.asymptotics.negligable

/-!
# Hash Functions

This file defines a basic version of a hash function.

-/

open oracle_comp oracle_spec

/-- `keygen` takes in a security parameter and outputs a key bundled with the parameter
  `hash` takes a `hash_key` and a string in the input space to a string in the output space -/
structure hash_function (K I O : Type) :=
(keygen : unit → oracle_comp coin_spec K)
(hash : K × I → O)
-- (keygen_poly_time : poly_time_oracle_comp keygen)
-- (hash_poly_time : poly_time hash)

namespace hash_function

variables {K I O : Type} (h : hash_function K I O)

variables [decidable_eq O]

/-- The security game for collision resistance as a probabalistic function. -/
def collision_finding_experiment (h : hash_function K I O)
  (adversary : K → oracle_comp coin_spec (I × I)) : oracle_comp coin_spec bool := 
do{ k ← (h.keygen ()),
    xs ← (adversary k),
    return (h.hash (k, xs.1) = h.hash (k, xs.2)) }

end hash_function

def hash_scheme (K I O : ℕ → Type) :=
Π (sp : ℕ), hash_function (K sp) (I sp) (O sp)

namespace hash_scheme

variables {K I O : ℕ → Type} {H : hash_scheme K I O}

variables [∀ n, decidable_eq $ O n]

structure collision_finding_adversary (H : hash_scheme K I O) :=
(adv : Π (sp : ℕ), K sp → oracle_comp coin_spec ((I sp) × (I sp)))
(adv_poly_time : ∀ sp, poly_time_oracle_comp $ adv sp)

/-- Collision resistant if all polynomial time adversaries have neglibable chance
  of winning the `collision_finding_experiment` as the security parameter increases -/
def collision_resistant (H : hash_scheme K I O) : Prop :=
∀ (adversary : collision_finding_adversary H),
negligable (λ sp, ⦃(H sp).collision_finding_experiment (adversary.adv sp)⦄ tt)

end hash_scheme