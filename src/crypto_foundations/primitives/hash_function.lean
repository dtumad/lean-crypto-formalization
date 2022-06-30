import computational_monads.distribution_semantics.prob_event
import computational_monads.oracle_spec
import computational_monads.asymptotics.polynomial_time

open oracle_comp oracle_spec

/-!
# Hash Functions

This file defines the notion of a keyed hash function.

-/

structure hash_function (K I O : Type) :=
(keygen : unit → oracle_comp coin_oracle K)
(hash : K × I → O)
(keygen_poly_time : poly_time_oracle_comp keygen)
(hash_poly_time : poly_time hash)

namespace hash_function

variables {K I O : Type} (h : hash_function K I O)

variables [decidable_eq O]

/-- The security game for collision resistance as a probabalistic function. -/
def collision_finding_experiment (h : hash_function K I O)
  (A : K → oracle_comp coin_oracle (I × I)) : oracle_comp coin_oracle bool := 
do{ k ← (h.keygen ()),
    xs ← (A k),
    return (h.hash (k, xs.1) = h.hash (k, xs.2)) }

end hash_function

/-- `keygen` takes in a security parameter and outputs a key bundled with the parameter
  `hash` takes a `hash_key` from keygen and a string in the input space to a string in the output space
  TODO: Use better complexity model and public parameters model for this -/
def hash_scheme (K I O : ℕ → Type) :=
Π (sp : ℕ), hash_function (K sp) (I sp) (O sp)

namespace hash_scheme

variables {K I O : ℕ → Type} {H : hash_scheme K I O}

variables [∀ n, decidable_eq $ O n]

structure collision_finding_adversary (H : hash_scheme K I O) :=
(adv : Π (sp : ℕ), K sp → oracle_comp coin_oracle ((I sp) × (I sp)))
(adv_poly_time : ∀ sp, poly_time_oracle_comp $ adv sp)

def collision_resistant (H : hash_scheme K I O) : Prop :=
∀ (A : collision_finding_adversary H),
negligable (λ sp, ⟦(H sp).collision_finding_experiment (A.adv sp)⟧ tt)

end hash_scheme