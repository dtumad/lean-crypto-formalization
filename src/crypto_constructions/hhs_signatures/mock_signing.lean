/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_constructions.hhs_signatures.hhs_signature

/-!
# Mocking Signing Oracles for HHS Signatures

This file gives a way to mock the signing oracle for an adversary without an actual secret key.
-/

namespace hhs_signature

open_locale ennreal big_operators
open oracle_comp oracle_spec algorithmic_homogenous_space hard_homogenous_space

variables {G X M : Type} [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}

section unforgeable

section mock_signing_sim_oracle

/-- Oracle to mock a signing oracle for messages in the vectorization reduction,
mirroring how `signingₛₒ` would respond usually.
Predetermines the random oracle results to fake a valid signature,
keeping the results in a seperate internal mocked cache.
This also includes all caching for the simulation of the random oracles. -/
noncomputable def mock_signing_sim_oracle' (x₀ pk : X) : sim_oracle
  (uniform_selecting ++ (hhs_signature G X M n).random_spec ++ (hhs_signature G X M n).signing_spec)
  (uniform_selecting ++ (hhs_signature G X M n).random_spec)
  (query_cache ((vector X n × M) ↦ₒ vector bool n)) :=
{ default_state := ∅,
  o := λ i, match i with
    | (sum.inl (sum.inl i)) := λ ⟨t, mock_cache⟩,
        do { u ← query (sum.inl i) t,
          return (u, mock_cache) }
    -- For random oracle queries, check if the query has been mocked.
    -- If so, return the mocked value, otherwise call the regular oracle (caching the result).
    | (sum.inl (sum.inr i)) := λ ⟨t, mock_cache⟩, mock_cache.get_or_else i t
        (@query (hhs_signature G X M n).base_spec (sum.inr i) t)
    -- For queries to the signing oracle, pre-select a hash value and make a signature for that.
    -- Also update the mocked cache with the value chosen for the hash output.
    | (sum.inr ()) := λ ⟨m, mock_cache⟩,
        do {bs ← repeat ($ᵗ bool) n, cs ← repeat ($ᵗ G) n,
          ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
          mock_cache' ← return (mock_cache.cache_query () (ys, m) bs),
          return ((cs, bs), mock_cache')}
  end }

-- /-- Oracle to mock a signing oracle for messages in the vectorization reduction,
-- mirroring how `signingₛₒ` would respond usually.
-- Predetermines the random oracle results to fake a valid signature,
-- keeping the results in a seperate internal mocked cache.
-- This also includes all caching for the simulation of the random oracles. -/
-- noncomputable def mock_signing_sim_oracle (x₀ pk : X) : sim_oracle
--   ((hhs_signature G X M n).random_spec ++ (hhs_signature G X M n).signing_spec)
--   (uniform_selecting ++ (hhs_signature G X M n).random_spec)
--   (query_cache ((vector X n × M) ↦ₒ vector bool n)) :=
-- { default_state := ∅,
--   o := λ i, match i with
--     -- For random oracle queries, check if the query has been mocked.
--     -- If so, return the mocked value, otherwise call the regular oracle (caching the result).
--     | (sum.inl i) := λ ⟨t, mock_cache⟩, mock_cache.get_or_else i t
--         (@query (hhs_signature G X M n).base_spec (sum.inr i) t)
--     -- For queries to the signing oracle, pre-select a hash value and make a signature for that.
--     -- Also update the mocked cache with the value chosen for the hash output.
--     | (sum.inr ()) := λ ⟨m, mock_cache⟩,
--         do {bs ← repeat ($ᵗ bool) n, cs ← repeat ($ᵗ G) n,
--           ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
--           mock_cache' ← return (mock_cache.cache_query () (ys, m) bs),
--           return ((cs, bs), mock_cache')}
--   end }

alias mock_signing_sim_oracle' ← mock_signingₛₒ

-- #check mock_signingₛₒ

variables (x₀ pk : X)

-- lemma mock_signing_sim_oracle_apply_dist_equiv {α : Type}
--   (oa : oracle_comp ((uniform_selecting ++ (hhs_signature G X M n).random_spec) ++ (hhs_signature G X M n).signing_spec) α)
--   :
--   default_simulate (idₛₒ ++ₛ mock_signingₛₒ x₀ pk) oa ≃ₚ
--    default_simulate (idₛₒ ++ₛ mock_signingₛₒ x₀ pk) oa

end mock_signing_sim_oracle

-- noncomputable def mock_simulate_signing_oracle (adversary : (hhs_signature G X M n).unforgeable_adversary)
--   (x₀ pk : X) : oracle_comp (hhs_signature G X M n).base_spec
--     ((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_cache) :=
-- do {((m, σ), _, mocked_sigs) ← (default_simulate (idₛₒ ++ₛ mock_signingₛₒ x₀ pk) (adversary.run (x₀, pk))),
--   return ((m, σ), mocked_sigs)}

noncomputable def mocked_unforgeable_adversary
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  sec_adversary (hhs_signature G X M n).base_spec (X × X)
    ((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_cache) :=
{ run := λ ks, default_simulate (mock_signingₛₒ ks.1 ks.2) (adv.run ks),
  qb := ∅ } -- TODO: bound

noncomputable def mock_signing_unforgeable_experiment :
  base_sec_experiment (hhs_signature G X M n).base_spec (X × X)
    ((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_cache) :=
base_sec_experiment_of_is_valid (prod.fst <$> (hhs_signature G X M n).gen ())
  (λ ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, cache⟩, begin
    let ys : vector X n := retrieve_commits x₀ pk zs hash,
    let hash' := cache.lookup () (ys, m),
    refine return (some hash = hash'),
  end)

end unforgeable

end hhs_signature