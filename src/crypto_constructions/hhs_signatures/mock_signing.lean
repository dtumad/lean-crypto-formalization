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

variables {G X M : Type} [fintype G] [fintype X] [inhabited G] [inhabited X]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

section unforgeable

-- section mock_signing

/-- Oracle to mock a signing oracle for messages in the vectorization reduction,
mirroring how `signingₛₒ` would respond usually.
Predetermines the random oracle results to fake a valid signature,
keeping the results in a seperate internal mocked cache.
This also includes all caching for the simulation of the random oracles. -/
noncomputable def mock_signingₛₒ (x₀ pk : X) : sim_oracle
  ((hhs_signature G X M n).random_spec ++ (hhs_signature G X M n).signing_spec)
  (uniform_selecting ++ (hhs_signature G X M n).random_spec)
  (query_cache ((vector X n × M) ↦ₒ vector bool n)) :=
{ default_state := ∅,
  o := λ i, match i with
    -- For random oracle queries, check if the query has been mocked.
    -- If so, return the mocked value, otherwise call the regular oracle (caching the result).
    | (sum.inl i) := λ ⟨t, mock_cache⟩, mock_cache.get_or_else i t
        (@query (hhs_signature G X M n).base_spec (sum.inr i) t)
    | (sum.inr ()) := λ ⟨m, mock_cache⟩,
        do {bs ← repeat ($ᵗ bool) n, cs ← repeat ($ᵗ G) n,
          ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
          mock_cache' ← return (mock_cache.cache_query () (ys, m) bs),
          return (vector.zip_with prod.mk cs bs, mock_cache')}
  end }

noncomputable def mock_simulate_signing_oracle (adversary : (hhs_signature G X M n).unforgeable_adversary)
  (x₀ pk : X) : oracle_comp (hhs_signature G X M n).base_spec
    ((M × vector (G × bool) n) × (hhs_signature G X M n).random_spec.query_cache) :=
do {((m, σ), _, mocked_sigs) ← (default_simulate (idₛₒ ++ₛ mock_signingₛₒ x₀ pk) (adversary.run (x₀, pk))),
  return ((m, σ), mocked_sigs)}

noncomputable def mock_signing_unforgeable_adversary :=
sec_adversary (hhs_signature G X M n).base_spec (X × X)
  ((M × vector (G × bool) n) × (hhs_signature G X M n).random_spec.query_cache)

noncomputable def mock_signing_unforgeable_adversary.experiment :
  sec_experiment (hhs_signature G X M n).base_spec
    (hhs_signature G X M n).base_spec
    (X × X) ((M × vector (G × bool) n) × (hhs_signature G X M n).random_spec.query_cache)
    unit unit :=
{ inp_gen := do {ks ← (hhs_signature G X M n).gen (), return (ks.1, ())},
  so := sorry,
  is_valid := sorry
}
-- def mocked_signing

noncomputable def mocked_unforgeable_adversary
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  sec_adversary (hhs_signature G X M n).base_spec (X × X)
    ((M × vector (G × bool) n) × (hhs_signature G X M n).random_spec.query_cache) :=
{ run := λ ks, do {
    ((m, σ), _, mocked_sigs) ← (default_simulate (idₛₒ ++ₛ mock_signingₛₒ ks.1 ks.2) (adv.run ks)),
    return ((m, σ), mocked_sigs)
  },
  qb := ∅ -- TODO
}

end unforgeable

end hhs_signature