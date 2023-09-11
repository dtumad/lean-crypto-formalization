/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.zip
import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.fork

/-!
# Signature Scheme Based On Hard Homogenous Spaces

This file defines a signature scheme based on hard homogenous spaces,
using a generalized version of the basic Schnorr signature scheme.

We prove both completeness and unforgeability, providing an explicit reduction
from signature forgery to a vectorization forgery.
-/

noncomputable theory

open_locale ennreal big_operators
open oracle_comp oracle_spec algorithmic_homogenous_space hard_homogenous_space

section commits

variables {G X M : Type} [fintype G] [fintype X]
  [decidable_eq G] [decidable_eq X]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

/-- Given a list of commitments `cs` and a hash value `h`, zip them together by adding
the security key to indices of `cs` corresponding to `0` bits in `h`. -/
@[reducible, inline] def zip_commits_with_hash (cs : vector G n)
  (h : vector bool n) (sk : G) : vector (G × bool) n :=
vector.zip_with (λ c (b : bool), (if b then c else c + sk, b)) cs h

/-- Given a pair of points `x₀` and `pk`, attempt to retreive the commits from a signature `σ`,
by adding the vactor to either `pk` or `x₀` depending on if the entry would have had `sk` added.
Will result in `(cs.map (+ᵥ pk))` if the original signature is valid. -/
@[reducible, inline] def retrieve_commits (x₀ pk : X)
  (σ : vector (G × bool) n) : vector X n :=
(σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀))

/-- `retrieve_commits` will succeed if every hash bit is `0` or if `sk` is a true vectorization. -/
@[simp] lemma retrieve_commits_zip_commits_with_hash_eq_iff (cs : vector G n)
  (h : vector bool n) (sk : G) (x₀ pk : X) :
  (retrieve_commits x₀ pk (zip_commits_with_hash cs h sk) = (cs.map (+ᵥ pk)))
    ↔ h = vector.replicate n tt ∨ sk +ᵥ x₀ = pk :=
begin
  sorry
end

end commits

/-- Schnorr signature derived from a hard homogenous space, based on the diffie helmann case.
`X` is the space of base points in the HHS, and `G` is the space of vectors between them.
`n` represents the number of commitments to make, more corresponding to more difficult forgery.
Public keys are pairs `(x₀, pk)` of a base point and a key point.
The secret key is the vectorization between the points `x₀` and `pk`, as an element of `G`.
We use a random oracle `(vector X n × M) ↦ₒ vector bool n` to hash the commitment values. -/
def hhs_signature (G X M : Type) (n : ℕ) [fintype G] [fintype X] [inhabited G] [inhabited X]
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
  random_oracle_spec := (vector X n × M) ↦ₒ vector bool n,
  decidable_eq_M := by apply_instance, decidable_eq_S := by apply_instance,
  inhabited_S := by apply_instance, fintype_S := by apply_instance }

namespace hhs_signature

variables {G X M : Type} [fintype G] [fintype X] [inhabited G] [inhabited X]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

local notation `hhssig` := hhs_signature G X M n

section apply

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

end apply

section complete

section is_valid_signature

/-- Check if a signature is valid, given an explicit internal state of the random oracle.
Note that we return `false` for things not-previously queried,
which differs from e.g. the behaviour of the actual `unforgeable` experiment. -/
def is_valid_signature (x₀ pk : X) (m : M) (σ : vector (G × bool) n)
  (cache : query_cache ((vector X n × M) ↦ₒ vector bool n)) : Prop :=
match cache.lookup () (retrieve_commits x₀ pk σ, m) with
| none := true
| (some h) := h = σ.map prod.snd
end

/-- Sign always returns valid signatures, in terms of the final random oracle state. -/
lemma is_valid_signature_of_mem_support_sign (x₀ pk : X) (sk : G) (m : M)
  (σ : vector (G × bool) n) (cache : query_cache ((vector X n × M) ↦ₒ vector bool n))
  (h : (σ, (), cache) ∈ (default_simulate (idₛₒ ++ₛ randomₛₒ) $
    (hhs_signature G X M n).sign ((x₀, pk), sk, m)).support) :
  is_valid_signature x₀ pk m σ cache :=
begin
  sorry
end

/-- Given a valid signature for some random oracle state, verify returns true
assuming the state is initialized with that cache. -/
lemma support_verify_of_is_valid_signature (x₀ pk : X) (m : M)
  (σ : vector (G × bool) n) (cache : query_cache ((vector X n × M) ↦ₒ vector bool n))
  (h : is_valid_signature x₀ pk m σ cache) : (simulate (idₛₒ ++ₛ randomₛₒ)
    ((hhs_signature G X M n).verify ((x₀, pk), m, σ)) ((), cache)).support = {(tt, (), cache)} :=
begin
  sorry
end

end is_valid_signature

theorem hhs_signature_complete [inhabited G] :
  (hhs_signature G X M n).complete :=
begin
  rw signature.complete_iff_signatures_support_subset,
  rintros m ⟨x₀, pk⟩ sk σ hgen hsign,
  sorry
end

end complete






section unforgeable

variables (adversary : (hhs_signature G X M n).unforgeable_adversary)

section mock_signing_oracle

/-- Oracle to mock a signing oracle for messages in the vectorization reduction.
Predetermines the random oracle results to fake a valid signature,
keeping the results in a seperate internal mocked cache.
Queries to the random oracle are first filtered through this,
and are passed to the true random oracle only if the query is fresh. -/
def mock_signing_sim_oracle (x₀ pk : X) :
  sim_oracle (hhs_signature G X M n).unforgeable_adversary_oracle_spec
  (hhs_signature G X M n).base_oracle_spec
  (query_cache ((vector X n × M) ↦ₒ vector bool n)) :=
{ default_state := ∅,
  o := λ i, match i with
    -- For random oracle queries, check if the query has been mocked.
    -- If so, return the mocked value, otherwise call the regular random oracle
    | (sum.inl i) := λ ⟨t, mock_cache⟩, mock_cache.get_or_else i t
        (@query (hhs_signature G X M n).base_oracle_spec (sum.inr i) t)
    | (sum.inr ()) := λ ⟨m, mock_cache⟩,
      do {bs ← repeat ($ᵗ bool) n, -- pre-select what all the bool results will be.
          cs ← repeat ($ᵗ G) n,
          ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
          mock_cache' ← return (mock_cache.cache_query () (ys, m) bs),
          return (vector.zip_with prod.mk cs bs, mock_cache')}
  end }

end mock_signing_oracle

section mock_signing_reduction

/-- Fake the signing oracle, and force a query corresponding to adversary's result. -/
def mock_signing_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary)
  (x₀ pk : X) : oracle_comp (hhs_signature G X M n).base_oracle_spec (M × vector (G × bool) n) :=
do{ ⟨m, σ⟩ ← default_simulate' (idₛₒ ++ₛ mock_signing_sim_oracle x₀ pk) (adversary.run (x₀, pk)),
    _ ← query₂ () (retrieve_commits x₀ pk σ, m), -- force a query to the final output
    return (m, σ) }

/-- Further simulate the random oracle after mocking the signing oracle -/
def simulate_mock_signing_reduction (pk x₀ : X) :
  oracle_comp uniform_selecting (M × vector (G × bool) n ×
    query_cache (hhs_signature G X M n).random_oracle_spec) :=
do{ ⟨⟨m, σ⟩, (), cache⟩ ← default_simulate (idₛₒ ++ₛ randomₛₒ)
      (mock_signing_reduction adversary x₀ pk),
    return (m, σ, cache) }

-- theorem prob_event_is_valid_signature_ge_unforgeable_advantage (x₀ pk : X) :
--   ⁅λ ⟨m, σ, cache⟩, is_valid_signature x₀ pk m σ cache |
--     simulate_mock_signing_reduction adversary x₀ pk⁆
--       ≥ adversary.advantage :=
-- begin
--   sorry
-- end

end mock_signing_reduction

section choose_fork

-- Note that if the message was queried to signing oracle (causing the experiment to fail
-- for unforgeability), then the result will only be in the higher level cache,
-- not the lower level one being used here (since it never leaves the "mock") -/
-- def choose_fork (x₀ pk : X) (m : M) (σ : vector (G × bool) n)
--   (cache : query_log (hhs_signature G X M n).random_oracle_spec) (q : ℕ) : option (fin q) :=
-- match cache.lookup () (retrieve_commits x₀ pk σ, m) with
-- | none := none
-- | (some ⟨h, index⟩) := if hq : index < q ∧ h = σ.map prod.snd then some ⟨index, hq.1⟩ else none
-- end

-- def choose_input (x₀ pk : X) (m : M) (σ : vector (G × bool) n) :
--   (hhs_signature G X M n).random_oracle_spec.domain () :=
-- (retrieve_commits x₀ pk σ, m)

end choose_fork

section fork_reduction

def mocked_unforgeable_adversary (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  sec_adversary ((hhs_signature G X M n).base_oracle_spec) (X × X)
    (M × vector (G × bool) n) :=
{ run := λ ⟨x₀, pk⟩, mock_signing_reduction adversary x₀ pk,
  qb := sorry,
  qb_is_bound := sorry }

/-- Reduce an unforgeability adversery to a forking adversary that can be passed to
`oracle_comp.fork` to get two results, that can be used to construct a adversary for
vectorization in the hard homogenous space.
`q` is the maximum number of queries made by the adversary to consider. -/
def fork_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  fork_adversary (X × X) ((M × vector (G × bool) n) × _) _ _ :=
forking_adversary.of_choose_input (mocked_unforgeable_adversary adversary) ()
  (λ z y, (retrieve_commits z.1 z.2 y.2, y.1))

-- lemma advantage_le_forking_reduction_advantage
--   (adversary : (hhs_signature G X M n).unforgeable_adversary) (x₀ pk : X) :
--     adversary.advantage ≤ (fork_reduction adversary).advantage (x₀, pk) :=
-- begin
--   sorry
-- end

/-- If the fork succeeds, we know that there are two valid signatures
corresponding to a query with the same input and a different output.
This further implies that `retrieve_commits` agrees on both,
but the actual booleans are different, which will let us get a vectorization. -/
theorem vectorizable_of_fork_success'' (x₀ pk : X)
  (fr : fork_result (fork_reduction adversary)) (hfr : fork_success fr)
  (h : fr ∈ (fork (fork_reduction adversary) (x₀, pk)).support) :
  retrieve_commits x₀ pk fr.side_output₁.1.2 = retrieve_commits x₀ pk fr.side_output₂.1.2
    ∧ fr.side_output₁.1.2.map prod.snd ≠ fr.side_output₂.1.2.map prod.snd :=
begin
  sorry
end

/-- The probability of the fork succeeding is at least the square of
the original adversary's success probability, minus a small chance
of both oracle calls giving the same result. -/
theorem le_prob_event_fork_success (x₀ pk : X) :
  (adversary.advantage ^ 2 / (adversary.qb.get_count (sum.inr (sum.inr ())))) - (1 / 2 ^ n) ≤
    ⁅fork_success | fork (fork_reduction adversary) (x₀, pk)⁆ :=
begin
  sorry
end

-- def vectorization_of_commits ()


-- /-- If the fork succeeds, we know that there are two valid signatures
-- corresponding to a query with the same input and a different output.
-- This further implies that `retrieve_commits` agrees on both,
-- but the actual booleans are different, which will let us get a vectorization. -/
-- theorem vectorizable_of_fork_success (x₀ pk : X)
--   (fr : fork_result (fork_reduction adversary)) (hfr : fork_success fr)
--   (h : fr ∈ (fork (fork_reduction adversary) (x₀, pk)).support) :
--   vectorization_of_fork_result _ x₀ pk fr = pk -ᵥ x₀ :=
-- begin
--   sorry
-- end

end fork_reduction

section vectorization_reduction

def vectorization_of_fork_result (adv : (hhs_signature G X M n).unforgeable_adversary)
  (x₀ pk : X) (fr : fork_result (fork_reduction adv)) : G :=
begin
  let σ₁ := fr.side_output₁.1.2,
  let σ₂ := fr.side_output₂.1.2,
  let ys₁ := retrieve_commits x₀ pk fr.side_output₁.1.2,
  let ys₂ := retrieve_commits x₀ pk fr.side_output₂.1.2,
  let h₁ := fr.side_output₁.1.2.map prod.snd,
  let h₂ := fr.side_output₂.1.2.map prod.snd,
  let m : fin n := sorry,
  exact (σ₁.nth m).1 - (σ₂.nth m).1
end

def vectorization_reduction (adv : (hhs_signature G X M n).unforgeable_adversary) :
  vectorization_adversary G X :=
{ run :=
  begin
    rintro ⟨x₀, pk⟩,
    have := default_simulate' (idₛₒ ++ₛ randomₛₒ) (fork (fork_reduction adv) (x₀, pk)),
    refine vectorization_of_fork_result _ x₀ pk <$> this,
  end
  ,
  qb := sorry,
  qb_is_bound := sorry,
}

/-- The probability of the fork succeeding is at least the square of
the original adversary's success probability, minus a small chance
of both oracle calls giving the same result. -/
theorem le_vectorization_advantage (x₀ pk : X) :
  (adversary.advantage ^ 2 / (adversary.qb.get_count (sum.inr (sum.inr ())))) - (1 / 2 ^ n) ≤
    (vectorization_reduction adversary).advantage :=
begin
  sorry
end

end vectorization_reduction

end unforgeable

end hhs_signature