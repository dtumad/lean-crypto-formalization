-- /-
-- Copyright (c) 2022 Devon Tuma. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Devon Tuma
-- -/
-- import crypto_constructions.hhs_signatures.hhs_signature
-- import computational_monads.query_tracking.query_count.is_query_bound
-- import computational_monads.simulation_semantics.oracle_append

-- /-!
-- # Mocking Signing Oracles for HHS Signatures

-- This file gives a way to mock the signing oracle for an adversary without an actual secret key.
-- -/

-- namespace hhs_signature

-- open oracle_comp oracle_spec
-- open sum (inl) (inr)
-- open_locale ennreal big_operators

-- variables {α G X M : Type} [decidable_eq M]
--   [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}

-- section state_types

-- @[derive [decidable_eq, inhabited]]
-- structure signature_seed (G X : Type) (n : ℕ) :=
-- (query_index : ℕ)
-- (xs : vector X n)
-- (zs : vector G n)
-- (bs : vector bool n)

-- structure mock_cache_entry (G X M : Type) (n : ℕ)
--   extends signature_seed G X n := (m : M)

-- def lookup_mock_cache {G X M : Type} {n : ℕ} [decidable_eq M] [decidable_eq X]
--   (mock_cache : list (mock_cache_entry G X M n))
--   (xs : vector X n) (m : M) : option (mock_cache_entry G X M n) :=
-- mock_cache.find (λ mc, mc.xs = xs ∧ mc.m = m)

-- end state_types

-- noncomputable def mock_signing_oracle (x₀ pk : X) :
--   sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
--     (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
--     ((vector X n × M) ↦ₒ vector bool n).query_log :=
-- λ i, match i with
-- /- For queries to the uniform selection oracle, just forward the queries. -/
-- | (inl (inl i)) := λ ⟨t, s⟩, do
--     {u ← query (inl i) t, return (u, s)}
-- /- For queries to the random oracle, look at the mocked cache. -/
-- | (sum.inl (inr ())) := λ ⟨⟨xs, m⟩, mock_cache⟩,
--   match mock_cache.lookup () (xs, m) with
--   | (some bs) := return (bs, mock_cache)
--   | none := do { bs ←$ᵗ (vector bool n),
--       return (bs, mock_cache.log_query () (xs, m) bs) }
--   end
-- /- For queries to the signing oracle, pre-choose the query result,
--   and insert into the cache. "Fails" if `xs` isn't fresh. -/
-- | (sum.inr ()) := λ ⟨m, mock_cache⟩, do
--     { zs ←$ᵗ (vector G n), bs ←$ᵗ (vector bool n),
--       let xs := unzip_commits x₀ pk zs bs in
--       return ((zs, bs), mock_cache.log_query () (xs, m) bs) }
-- end

-- alias mock_signing_oracle ← mock_signingₛₒ

-- namespace mock_signing_oracle

-- -- #check (hhs_signature G X M n).unforgeable_adv_spec
-- -- #check unif_spec ++ (vector X n × M ↦ₒ vector bool n) ++ (M ↦ₒ vector G n × vector bool n)

-- lemma prob_bound [algorithmic_homogenous_space G X]
--   (x₀ pk : X) (oa : oracle_comp (hhs_signature G X M n).unforgeable_adv_spec α)
--   (z : α) (cache : query_log ((vector X n × M) ↦ₒ vector bool n))
--   (qc : query_count (hhs_signature G X M n).unforgeable_adv_spec)
--   (h : is_query_bound oa qc) :
--   ⁅= z | simulate' (sim_oracle.compose (identity_oracle unif_spec ++ₛₒ randomₛₒ)
--     (identity_oracle (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n)) 
--       ++ₛₒ (hhs_signature G X M n).signingₛₒ (x₀, pk) (pk -ᵥ x₀))) oa (((), ∅), (), cache)⁆
--     * (1 - 1 / sorry) ≤
--     ⁅= z | simulate' (mock_signingₛₒ x₀ pk) oa cache⁆  :=
-- begin
--   sorry,
-- end

-- section apply

-- -- TODO

-- end apply

-- end mock_signing_oracle

-- section generate_sig_seed

-- noncomputable def generate_sig_seed (x₀ pk : X) (m : ℕ) : Π (k : ℕ),
--   oracle_comp unif_spec (list (signature_seed G X n))
-- | 0 := return (list.nil)
-- | (k + 1) := list.cons <$>
--   (do {zs ←$ᵗ (vector G n), bs ←$ᵗ (vector bool n),
--       return ⟨m - (k + 1), unzip_commits x₀ pk zs bs, zs, bs⟩})
--     <*> generate_sig_seed k

-- end generate_sig_seed

-- section mock_signing

-- -- noncomputable def mock_signing_aux
-- --   (oa : oracle_comp (hhs_signature G X M n).unforgeable_adv_spec α)
-- --   (x₀ pk : X) (k : ℕ) : oracle_comp (unif_spec ++ (unit ↦ₒ vector bool n))
-- --     (α × list (mock_cache_entry G X M n)) :=
-- -- do {sig_seed ← @generate_sig_seed G X _ _ n x₀ pk k k,
-- --   z ← simulate (mock_signingₛₒ x₀ pk) oa (k, sig_seed, list.nil),
-- --   return (z.1, z.2.2.2)}

-- -- noncomputable def mock_signing (oa : oracle_comp (hhs_signature G X M n).unforgeable_adv_spec α)
-- --   (x₀ pk : X) : oracle_comp (unif_spec ++ (unit ↦ₒ vector bool n))
-- --     (α × list (mock_cache_entry G X M n)) :=
-- -- let k : ℕ := (query_bound oa).get_count (inl (inr ())) + (query_bound oa).get_count (inr ()) in
-- -- mock_signing_aux oa x₀ pk ((query_bound oa).get_count (inr ()))

-- end mock_signing

-- section mock_signing_qb

-- def mock_signing_qb (qb : (hhs_signature G X M n).unforgeable_adv_spec.query_count) :
--   (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n)).query_count :=
-- (qb.reduce (λ i, sum.rec_on i (sum.map id (λ _, ())) (λ _, sum.inr ())))

-- -- def mock_signing_qb_is_query_bound
-- --   (oa : oracle_comp (hhs_signature G X M n).unforgeable_adv_spec α)
-- --   (x₀ pk : X) (qb : (hhs_signature G X M n).unforgeable_adv_spec.query_count)
-- --   (hqb : is_query_bound oa qb) : is_query_bound (mock_signing oa x₀ pk) (mock_signing_qb qb) :=
-- -- begin
-- --   sorry
-- -- end

-- end mock_signing_qb

-- end hhs_signature