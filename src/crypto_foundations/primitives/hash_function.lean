/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.sec_experiment

/-!
# Hash Functions

This file defines a basic version of a hash function and collision resistance.
-/

open oracle_comp oracle_spec

structure hash_function (spec : oracle_spec) (K I O : Type)
  extends oracle_algorithm spec :=
(keygen : unit → oracle_comp spec K)
(hash : K × I → O)

namespace hash_function

variables {spec : oracle_spec} {K I O : Type} [decidable_eq O]

def collision_finding_adv (hf : hash_function spec K I O) :=
sec_adv spec K (I × I)

def collision_finding_exp {hf : hash_function spec K I O}
  (adv : collision_finding_adv hf) : sec_exp spec K (I × I) :=
{ inp_gen := hf.keygen (),
  main := adv.run,
  is_valid := λ k ⟨m, m'⟩, hf.hash (k, m) = hf.hash (k, m'),
  .. hf }

end hash_function

def hash_scheme (spec : ℕ → oracle_spec) (K I O : ℕ → Type) :=
Π (sp : ℕ), hash_function (spec sp) (K sp) (I sp) (O sp)

namespace hash_scheme

open hash_function

variables {spec : ℕ → oracle_spec} {K I O : ℕ → Type}
  [∀ n, decidable_eq $ O n]

/-- Collision resistant if all polynomial time adversaries have neglibable chance
  of winning the `collision_finding_experiment` as the security parameter increases -/
def collision_resistant (hf : hash_scheme spec K I O) : Prop :=
∀ (adv : Π (sp : ℕ), (hf sp).collision_finding_adv),
negligable (λ sp, (collision_finding_exp (adv sp)).advantage)

end hash_scheme