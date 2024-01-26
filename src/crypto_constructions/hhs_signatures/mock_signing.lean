/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_constructions.hhs_signatures.hhs_signature
import computational_monads.query_tracking.query_count.is_query_bound

/-!
# Mocking Signing Oracles for HHS Signatures

This file gives a way to mock the signing oracle for an adversary without an actual secret key.
-/

namespace hhs_signature

open oracle_comp oracle_spec
open sum (inl) (inr)
open_locale ennreal big_operators

variables {α G X M : Type} [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}

section state_types

@[derive [decidable_eq, inhabited]]
structure signature_seed (G X : Type) (n : ℕ) :=
(query_index : ℕ)
(xs : vector X n)
(zs : vector G n)
(bs : vector bool n)

structure mock_cache_entry (G X M : Type) (n : ℕ)
  extends signature_seed G X n := (m : M)

def lookup_mock_cache {G X M : Type} {n : ℕ} [decidable_eq M] [decidable_eq X]
  (mock_cache : list (mock_cache_entry G X M n))
  (xs : vector X n) (m : M) : option (mock_cache_entry G X M n) :=
mock_cache.find (λ mc, mc.xs = xs ∧ mc.m = m)

end state_types

noncomputable def mock_signing_oracle (x₀ pk : X) :
  sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
    (unif_spec ++ (unit ↦ₒ vector bool n))
    (ℕ × list (signature_seed G X n) × list (mock_cache_entry G X M n)) :=
λ i, match i with
| (sum.inl (sum.inl i)) := λ ⟨t, s⟩,
  --For queries to the uniform selection oracle, just forward the queries.
  do {u ← query (sum.inl i) t, return (u, s)}
| (sum.inl (sum.inr ())) := λ ⟨⟨xs, m⟩, k, sig_seed, mock_cache⟩,
  -- For queries to the random oracle, first check if this value has already been cached.
  match lookup_mock_cache mock_cache xs m with
    | (some mc) := return (mc.bs, k, sig_seed, mock_cache)
      -- If not, check if this input is seeded for use by the signing oracle
    | none := match sig_seed.find ((= xs) ∘ signature_seed.xs) with
      | (some seed) := return (seed.bs, k, sig_seed.erase seed,
          {m := m, .. seed} :: mock_cache)
        -- If not, generate a new hash value and increment the counter
      | none := do {bs ←$ᵗ (vector bool n),
          return (bs, k + 1, sig_seed,
            ⟨⟨k, xs, default, bs⟩, m⟩ :: mock_cache)}
    end
  end
| (sum.inr ()) := λ ⟨m, k, sig_seed, mock_cache⟩,
  -- For queries to the signing oracle, take the first pre-seed from the seed list.
  let seed := sig_seed.head in
  -- Check if the inputs are already cached, and if so return the signature from there.
  match lookup_mock_cache mock_cache seed.xs m with
  | (some mc) := return ((mc.zs, mc.bs), k, sig_seed.tail, mock_cache)
    -- Otherwise, use the pre-seed values to generate a new signature.
  | none := return ((seed.zs, seed.bs), k, sig_seed.tail,
      {m := m, .. seed} :: mock_cache)
  end
end

alias mock_signing_oracle ← mock_signingₛₒ

namespace mock_signing_oracle

section apply

-- TODO

end apply

end mock_signing_oracle

section generate_sig_seed

noncomputable def generate_sig_seed (x₀ pk : X) (m : ℕ) : Π (k : ℕ),
  oracle_comp unif_spec (list (signature_seed G X n))
| 0 := return (list.nil)
| (k + 1) := list.cons <$>
  (do {zs ←$ᵗ (vector G n), bs ←$ᵗ (vector bool n),
      return ⟨m - (k + 1), retrieve_commits x₀ pk zs bs, zs, bs⟩})
    <*> generate_sig_seed k

end generate_sig_seed

section mock_signing

noncomputable def mock_signing_aux
  (oa : oracle_comp (hhs_signature G X M n).unforgeable_adv_spec α)
  (x₀ pk : X) (k : ℕ) : oracle_comp (unif_spec ++ (unit ↦ₒ vector bool n))
    (α × list (mock_cache_entry G X M n)) :=
do {sig_seed ← @generate_sig_seed G X _ _ n x₀ pk k k,
  z ← simulate (mock_signingₛₒ x₀ pk) oa (k, sig_seed, list.nil),
  return (z.1, z.2.2.2)}

noncomputable def mock_signing (oa : oracle_comp (hhs_signature G X M n).unforgeable_adv_spec α)
  (x₀ pk : X) : oracle_comp (unif_spec ++ (unit ↦ₒ vector bool n))
    (α × list (mock_cache_entry G X M n)) :=
let k : ℕ := (query_bound oa).get_count (inl (inr ())) + (query_bound oa).get_count (inr ()) in
mock_signing_aux oa x₀ pk ((query_bound oa).get_count (inr ()))

end mock_signing

section mock_signing_qb

def mock_signing_qb (qb : (hhs_signature G X M n).unforgeable_adv_spec.query_count) :
  (unif_spec ++ (unit ↦ₒ vector bool n)).query_count :=
(qb.reduce (λ i, sum.rec_on i (sum.map id (λ _, ())) (λ _, sum.inr ())))

def mock_signing_qb_is_query_bound
  (oa : oracle_comp (hhs_signature G X M n).unforgeable_adv_spec α)
  (x₀ pk : X) (qb : (hhs_signature G X M n).unforgeable_adv_spec.query_count)
  (hqb : is_query_bound oa qb) : is_query_bound (mock_signing oa x₀ pk) (mock_signing_qb qb) :=
begin
  sorry
end

end mock_signing_qb

end hhs_signature