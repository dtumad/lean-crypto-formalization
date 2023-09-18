/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.zip
import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.fork.fork
import crypto_constructions.hhs_signatures.commits

/-!
# Signature Scheme Based On Hard Homogenous Spaces

This file defines a signature scheme based on hard homogenous spaces,
using a generalized version of the basic Schnorr signature scheme.

We prove both completeness and unforgeability, providing an explicit reduction
from signature forgery to a vectorization forgery.
-/

open_locale ennreal big_operators
open oracle_comp oracle_spec prod algorithmic_homogenous_space

/-- Schnorr signature derived from a hard homogenous space, based on the diffie helmann case.
`X` is the space of base points in the HHS, and `G` is the space of vectors between them.
`n` represents the number of commitments to make, more corresponding to more difficult forgery.
Public keys are pairs `(x₀, pk)` of a base point and a key point.
The secret key is the vectorization between the points `x₀` and `pk`, as an element of `G`.
We use a random oracle `(vector X n × M) ↦ₒ vector bool n` to hash the commitment values. -/
noncomputable def hhs_signature (G X M : Type) (n : ℕ) [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] : signature :=
{ M := M, PK := X × X, SK := G, S := vector G n × vector bool n,
  -- Choose a public key by picking a random base point `x₀` and secret key `sk` (`pk` is forced).
  gen := λ _, do {x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk)},
  -- Sign a message by choosing `n` random commitments, and giving secret key proofs for each.
  sign := λ ⟨⟨x₀, pk⟩, sk, m⟩,
    do {(cs : vector G n) ← repeat ($ᵗ G) n,
      (ys : vector X n) ← return (cs.map (+ᵥ pk)),
      (hash : vector bool n) ← query₂ () (ys, m),
      return (zip_commits sk cs hash, hash)},
  -- Verify a signature by checking that the commitments map to the expected values.
  verify := λ ⟨⟨x₀, pk⟩, m, zs, hash⟩,
    do {(ys : vector X n) ← return (retrieve_commits x₀ pk zs hash),
      (hash' : vector bool n) ← query₂ () (ys, m),
      return (hash' = hash)},
  -- Random oracle allows a commitment to be mapped to a list of bools
  random_spec := (vector X n × M) ↦ₒ vector bool n,
  decidable_eq_M := by apply_instance, decidable_eq_S := by apply_instance,
  inhabited_S := by apply_instance, fintype_S := by apply_instance }

namespace hhs_signature

variables {G X M : Type} [decidable_eq M] [add_comm_group G]
  [algorithmic_homogenous_space G X] {n : ℕ}

@[simp] lemma random_spec_eq_singleton_spec :
  (hhs_signature G X M n).random_spec = ((vector X n × M) ↦ₒ vector bool n) := rfl

section gen

variables (u : unit)

@[simp] lemma gen_apply : ((hhs_signature G X M n).gen u) =
  do {x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk)} := rfl

lemma support_gen : ((hhs_signature G X M n).gen u).support =
  ⋃ (x₀ : X) (sk : G), {((x₀, sk +ᵥ x₀), sk)} :=
by simp only [gen_apply, support_bind, support_coe_sub_spec,
  support_uniform_select_fintype, support_return, set.Union_true]

end gen

section sign

variables (x₀ pk : X) (sk : G) (m : M)

@[simp] lemma sign_apply : ((hhs_signature G X M n).sign ((x₀, pk), sk, m)) =
  do {(cs : vector G n) ← repeat ($ᵗ G) n,
    (ys : vector X n) ← return (cs.map (+ᵥ pk)),
    (hash : vector bool n) ← query₂ () (ys, m),
    return (zip_commits sk cs hash, hash)} := rfl

-- @[simp] lemma support_sign : ((hhs_signature G X M n).sign ((x₀, pk), sk, m)).support =
--   ⋃ (cs : vector G n) (h : vector bool n), {zip_commits cs h sk} :=
-- sorry

end sign

section verify

variables (x₀ pk : X) (m : M) (zs : vector G n) (hash : vector bool n)

@[simp] lemma verify_apply : ((hhs_signature G X M n).verify ((x₀, pk), m, zs, hash)) =
  do {(ys : vector X n) ← return (retrieve_commits x₀ pk zs hash),
    (hash' : vector bool n) ← query₂ () (ys, m),
    return (hash' = hash)} := rfl

end verify

section is_valid

-- def is_valid_iff (x₀ pk : X) (m : M) (σ : vector (G × bool) n)
--   (cache : ((vector X n × M) ↦ₒ vector bool n).query_cache) :
--   (hhs_signature G X M n).is_valid (x₀, pk) m σ cache ↔
--     cache.lookup () (retrieve_commits x₀ pk σ, m) = some (σ.map snd) :=
-- begin
--   sorry
-- end

end is_valid

end hhs_signature