/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.zip
import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.fork.fork

/-!
# Signature Scheme Based On Hard Homogenous Spaces

This file defines a signature scheme based on hard homogenous spaces,
using a generalized version of the basic Schnorr signature scheme.

We prove both completeness and unforgeability, providing an explicit reduction
from signature forgery to a vectorization forgery.
-/

open_locale ennreal big_operators
open oracle_comp oracle_spec prod algorithmic_homogenous_space hard_homogenous_space

section commits

variables {G X M : Type} [fintype G] [fintype X]
  [decidable_eq G] [decidable_eq X]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

/-- Given a list of commitments `cs` and a hash value `h`, zip them together by adding
the security key to indices of `cs` corresponding to `0` bits in `h`. -/
@[reducible, inline] def zip_commits_with_hash (cs : vector G n)
  (h : vector bool n) (sk : G) : vector (G × bool) n :=
vector.zip_with (λ c b, (if b = tt then c else c + sk, b)) cs h

/-- Given a pair of points `x₀` and `pk`, attempt to retreive the commits from a signature `σ`,
by adding the vactor to either `pk` or `x₀` depending on if the entry would have had `sk` added.
Will result in `(cs.map (+ᵥ pk))` if the original signature is valid. -/
@[reducible, inline] def retrieve_commits (x₀ pk : X)
  (σ : vector (G × bool) n) : vector X n :=
(σ.map (λ s, if s.2 = tt then s.1 +ᵥ pk else s.1 +ᵥ x₀))

lemma nth_retrieve_commits_zip_commits_with_hash (x₀ pk : X)
  (cs : vector G n) (hv : vector bool n) (sk : G) (i : fin n) :
  (retrieve_commits x₀ pk (zip_commits_with_hash cs hv sk)).nth i =
    if hv.nth i = tt then cs.nth i +ᵥ pk else (cs.nth i + sk) +ᵥ x₀:=
by by_cases hv : hv.nth i = tt; simp [hv]

/-- `retrieve_commits` will succeed if every hash bit is `0` or if `sk` is a true vectorization. -/
@[simp] lemma retrieve_commits_zip_commits_with_hash_eq_iff (x₀ pk : X)
  (cs : vector G n) (hv : vector bool n) (sk : G) :
  (retrieve_commits x₀ pk (zip_commits_with_hash cs hv sk) = (cs.map (+ᵥ pk))) ↔
    hv = vector.replicate n tt ∨ sk +ᵥ x₀ = pk :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    rw [zip_commits_with_hash, retrieve_commits] at h,
    have : ∃ i, vector.nth hv i = ff := sorry,

    rw [imp_iff_not]
  }
end

end commits

/-- Schnorr signature derived from a hard homogenous space, based on the diffie helmann case.
`X` is the space of base points in the HHS, and `G` is the space of vectors between them.
`n` represents the number of commitments to make, more corresponding to more difficult forgery.
Public keys are pairs `(x₀, pk)` of a base point and a key point.
The secret key is the vectorization between the points `x₀` and `pk`, as an element of `G`.
We use a random oracle `(vector X n × M) ↦ₒ vector bool n` to hash the commitment values. -/
noncomputable def hhs_signature (G X M : Type) (n : ℕ) [fintype G] [fintype X] [inhabited G] [inhabited X]
  [decidable_eq G] [decidable_eq X] [decidable_eq M] [add_group G]
  [algorithmic_homogenous_space G X] : signature :=
{ M := M, PK := X × X, SK := G, S := vector (G × bool) n,
  -- Choose a public key by picking a random base point `x₀` and secret key `sk` (`pk` is forced).
  gen := λ _, do {x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk)},
  -- Sign a message by choosing `n` random commitments, and giving secret key proofs for each.
  sign := λ ⟨⟨x₀, pk⟩, sk, m⟩,
    do {(cs : vector G n) ← repeat ($ᵗ G) n,
      (ys : vector X n) ← return (cs.map (+ᵥ pk)),
      (h : vector bool n) ← query₂ () (ys, m),
      return (zip_commits_with_hash cs h sk)},
  -- Verify a signature by checking that the commitments map to the expected values.
  verify := λ ⟨⟨x₀, pk⟩, m, σ⟩,
    do {(ys : vector X n) ← return (retrieve_commits x₀ pk σ),
      (h : vector bool n) ← query₂ () (ys, m),
      return (h = σ.map prod.snd)},
  -- Random oracle allows a commitment to be mapped to a list of bools
  random_spec := (vector X n × M) ↦ₒ vector bool n,
  decidable_eq_M := by apply_instance, decidable_eq_S := by apply_instance,
  inhabited_S := by apply_instance, fintype_S := by apply_instance }

namespace hhs_signature

variables {G X M : Type} [fintype G] [fintype X] [inhabited G] [inhabited X]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

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
    (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
    (h : vector bool n) ← query₂ () (ys, m),
    return (zip_commits_with_hash cs h sk)} := rfl

@[simp] lemma support_sign : ((hhs_signature G X M n).sign ((x₀, pk), sk, m)).support =
  ⋃ (cs : vector G n) (h : vector bool n), {zip_commits_with_hash cs h sk} :=
sorry

end sign

section verify

variables (x₀ pk : X) (m : M) (σ : vector (G × bool) n)

@[simp] lemma verify_apply : ((hhs_signature G X M n).verify ((x₀, pk), m, σ)) =
  do {(ys : vector X n) ← return (retrieve_commits x₀ pk σ),
    (h : vector bool n) ← query₂ () (ys, m),
    return (h = σ.map prod.snd)} := rfl

end verify

section is_valid

def is_valid_iff (x₀ pk : X) (m : M) (σ : vector (G × bool) n)
  (cache : ((vector X n × M) ↦ₒ vector bool n).query_cache) :
  (hhs_signature G X M n).is_valid (x₀, pk) m σ cache ↔
    cache.lookup () (retrieve_commits x₀ pk σ, m) = some (σ.map snd) :=
begin
  sorry
end

end is_valid

end hhs_signature