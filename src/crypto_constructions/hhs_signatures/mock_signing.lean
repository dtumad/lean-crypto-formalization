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

open oracle_comp oracle_spec
open_locale ennreal big_operators

variables {G X M : Type} [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}

section mock_signing_sim_oracle

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

-- instance signature_seed.inhabited (G X : Type) (n : ℕ) [inhabited G] [inhabited X] :
--   inhabited (signature_seed G X n) :=
-- ⟨⟨0, vector.replicate n default, vector.replicate n default, vector.replicate n tt⟩⟩

noncomputable def mock_signing_sim_oracle (x₀ pk : X) :
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

noncomputable def generate_sig_seed (x₀ pk : X) (m : ℕ) : Π (k : ℕ),
  oracle_comp unif_spec (list (signature_seed G X n))
| 0 := return (list.nil)
| (k + 1) := list.cons <$>
  (do {zs ← repeat ($ᵗ G) n, bs ← repeat ($ᵗ bool) n,
      return ⟨m - (k + 1), retrieve_commits x₀ pk zs bs, zs, bs⟩})
    <*> generate_sig_seed k

def mock_signing_qb (adv_qb : query_count (hhs_signature G X M n).unforgeable_adv_spec) :
  query_count (unif_spec ++ (unit ↦ₒ vector bool n)) := sorry

noncomputable def mock_signing (adv : (hhs_signature G X M n).unforgeable_adv) :
  sec_adv (unif_spec ++ (unit ↦ₒ vector bool n)) (X × X)
    ((M × vector G n × vector bool n) × list (mock_cache_entry G X M n)) :=
{ run := λ ⟨x₀, pk⟩, let k : ℕ := (mock_signing_qb adv.run_qb).get_count (sum.inr ()) in
    do {sig_seed ← @generate_sig_seed G X _ _ n x₀ pk k k,
        z ← simulate (mock_signing_sim_oracle x₀ pk)
          (adv.run (x₀, pk)) (k, sig_seed, list.nil), 
        return (z.1, z.2.2.2)},
  run_qb := mock_signing_qb adv.run_qb }

end mock_signing_sim_oracle

end hhs_signature