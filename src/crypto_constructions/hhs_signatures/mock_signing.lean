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

section mock_signing_sim_oracle

#check list.find

-- noncomputable def mock_signing_sim_oracle'' (x₀ pk : X) :
--   sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
--     (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
--     _ :=
-- sim_oracle.comp _ (idₛₒ ++ₛ cachingₛₒ ++ₛ cachingₛₒ)

-- noncomputable def mock_signing_sim_oracle' (x₀ pk : X) :
--   sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
--     (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
--     (list ((vector X n × M) × vector bool n × option (vector G n))) :=
-- λ i, match i with
--   -- For queries to the uniform selection oracle, just forward the queries.
--   | (sum.inl (sum.inl i)) := λ ⟨t, mock_cache⟩, do
--       { u ← query (sum.inl i) t,
--         return (u, mock_cache) }
--   | (sum.inl (sum.inr ())) := λ ⟨⟨ys, m⟩, mock_cache⟩,
--       match mock_cache.find (λ z, prod.fst z = (ys, m)) with
--       | (some ⟨⟨xs, m⟩, bs, b⟩) := return (bs, mock_cache)
--       | none := do
--           { bs ← query (sum.inr ()) (ys, m),
--             return (bs, ((ys, m), bs, none) :: mock_cache) }
--       end
--   | (sum.inr ()) := λ ⟨m, mock_cache⟩, do
--       { bs ← repeat ($ᵗ bool) n,
--         cs ← repeat ($ᵗ G) n,
--         ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
--         mock_cache' ← return (mock_cache.log_query () (ys, m) bs),
--         return ((cs, bs), mock_cache') }

def signature_seed (G X : Type) (n : ℕ) :=
(list (vector bool n × vector G n))

@[inline, reducible] def mock_signing_state (G X M : Type) [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] (n b : ℕ) :=
(vector (vector bool n × vector G n) b)
  × (query_log ((vector X n × M) ↦ₒ vector bool n))

noncomputable def preseed_values (n b : ℕ) (x₀ pk : X) :
  oracle_comp unif_spec (signature_seed G X n) :=
vector.to_list <$> repeat (do
  { bs ← repeat ($ᵗ bool) n,
    zs ← repeat ($ᵗ G) n,
    return (bs, zs) }) b

-- def mock_signing_state (G X M : Type) [decidable_eq M] [add_comm_group G]
--   [algorithmic_homogenous_space G X] (n : ℕ) :=


-- -- noncomputable def init_mock_signing_state (G X : Type) [add_comm_group G]
-- --   [algorithmic_homogenous_space G X] (n b : ℕ) (x₀ pk : X) :
-- --   oracle_comp unif_spec (mock_signing_state G X M n b) :=
-- -- do {sig_seed ← repeat (do
-- --   { bs ← repeat ($ᵗ bool) n,
-- --     zs ← repeat ($ᵗ G) n,
-- --     return (bs, zs, retrieve_commits x₀ pk zs bs) }) b,
-- --   return (sig_seed, ∅) }

-- def mock_random_oracle (x₀ pk : X)
--   (mock_cache : query_log ((vector X n × M) ↦ₒ (vector bool n × vector G n)))
--   (seed : list (vector bool n × vector G n)) (ys : vector X n) (m : M) :
--   oracle_comp (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
--     (vector bool n) :=
-- do {
--   _
-- }

-- def mock_signing_sim_oracle' (x₀ pk : X) :
--   sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
--   (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
--   (query_log )

-- noncomputable def mock_signing_sim_oracle₃ (x₀ pk : X) :
--   sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
--   (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
--   (list (list M × vector X n × vector G n × vector bool n)) :=
-- λ i, match i with
-- | (sum.inl (sum.inl i)) := λ ⟨t, seed⟩, do
--     { u ← query (sum.inl i) t,
--       return (u, seed) }
--   -- For random oracle queries, check if the query has been mocked.
--   -- If so, return the mocked value, otherwise call the regular oracle (caching the result).
--   | (sum.inl (sum.inr ())) := λ ⟨⟨ys, m⟩, seed⟩,
--       match seed.find (λ z, prod.fst (prod.snd z) = ys) with
--       | (some (ms, ys, zs, bs)) := return (bs, seed.map _)
--       | _ := do {bs ← query (sum.inr ()) (ys, m), return (bs, seed)}
--       end
--   -- For queries to the signing oracle, pre-select a hash value and make a signature for that.
--   -- Also update the mocked cache with the value chosen for the hash output.
--   | (sum.inr ()) := λ ⟨m, seed⟩,
--       match seed.find (λ z, prod.fst z = list.nil) with
--       | (some (_, ys, zs, bs)) :=
--           match seed.find (λ z, )
--       | _ := _
--       end
-- end

open prod (fst) (snd)
open sum (inl) (inr)

def mock_signing_sim_oracle_k (x₀ pk : X) :
  sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
  (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
  (ℕ × list (vector X n × vector G n × vector bool n) ×
    query_log ((vector X n × M) ↦ₒ (vector G n × vector bool n))) :=
λ i, match i with
-- For queries to `unif_spec` just forward them through
| (inl (inl i)) := λ ⟨t, ⟨j, seed, cache⟩⟩, do
    { u ← query (inl i) t,
      return (u, (j, seed, cache)) }
| (inl (inr ())) := λ ⟨⟨ys, m⟩, ⟨j, seed, cache⟩⟩,
    -- Check if the query is already cached
    match cache.lookup () (ys, m) with
    | (some (zs, bs)) := return (bs, (j, seed, cache))
    | none :=
      -- Check if this `ys` is seeded already
      match seed.find (λ v, fst v = ys) with
      | (some (ys', zs, bs)) :=
          let seed' := seed.erase (ys', zs, bs) in
          return (bs, (j, seed', cache.log_query () (ys, m) (zs, bs)))
      | none := do
          { bs ← query (inr ()) (ys, m),
            return (bs, (j + 1, seed,
              cache.log_query () (ys, m) (default, bs)))}
      end
    end
| (inr ()) := λ ⟨m, ⟨j, seed, cache⟩⟩,
    -- Grab the next seed value
    match seed with
    | ((ys, zs, bs) :: seed') :=
      match cache.lookup () (ys, m) with
      | (some (zs', bs')) := 
          return ((zs', bs'), (j, seed', cache))
      | none :=
          return ((zs, bs), (j, seed', cache.log_query () (ys, m) (zs, bs)))
      end
    -- This case shouldn't happen in practice
    | list.nil := return default
    end
end


/-- Oracle to mock a signing oracle for messages in the vectorization reduction,
mirroring how `signingₛₒ` would respond usually.
Predetermines the random oracle results to fake a valid signature,
keeping the results in a seperate internal mocked cache.
This also includes all caching for the simulation of the random oracles. -/
noncomputable def mock_signing_sim_oracle (x₀ pk : X) :
  sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
  (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
  (query_log ((vector X n × M) ↦ₒ vector bool n)) :=
λ i, match i with
    -- For queries to the uniform selection oracle, just forward the queries.
    | (sum.inl (sum.inl i)) := λ ⟨t, mock_cache⟩, do
        { u ← query (sum.inl i) t,
          return (u, mock_cache) }
    -- For random oracle queries, check if the query has been mocked.
    -- If so, return the mocked value, otherwise call the regular oracle (caching the result).
    | (sum.inl (sum.inr i)) := λ ⟨t, mock_cache⟩,
        mock_cache.lookup_or_else i t (query i t)
    -- For queries to the signing oracle, pre-select a hash value and make a signature for that.
    -- Also update the mocked cache with the value chosen for the hash output.
    | (sum.inr ()) := λ ⟨m, mock_cache⟩, do
        { bs ← repeat ($ᵗ bool) n,
          zs ← repeat ($ᵗ G) n,
          ys ← return (retrieve_commits x₀ pk zs bs),
          mock_cache' ← return (mock_cache.log_query () (ys, m) bs),
          return ((zs, bs), mock_cache') }
  end

-- noncomputable def mock_signing_sim_oracle' (x₀ pk : X) :
--   sim_oracle (hhs_signature G X M n).full_spec
--   (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
--   ((vector X n × M) ↦ₒ vector bool n).query_log :=
-- { default_state := ∅,
--   o := λ i, match i with
--     -- For queries to the uniform selection oracle, just forward the queries.
--     | sum.inl (sum.inl i) := λ ⟨t, mock_cache⟩,
--         do {u ← query (sum.inl i) t,
--           return (u, mock_cache)}
--     -- For random oracle queries, imitate a random oracle using the mocked cache.
--     | sum.inl (sum.inr ()) := λ ⟨t, mock_cache⟩,
--         match mock_cache.lookup () t with
--         | none := do {u ← query (sum.inr ()) t, return (u, mock_cache.log_query () t u)}
--         | some u := return (u, mock_cache)
--         end
--         -- (@query (hhs_signature G X M n).base_spec (sum.inr i) t)
--     -- For queries to the signing oracle, pre-select a hash value and make a signature for that.
--     -- Also update the mocked cache with the value chosen for the hash output.
--     | sum.inr () := λ ⟨m, mock_cache⟩,
--         do {bs ← repeat ($ᵗ bool) n, cs ← repeat ($ᵗ G) n,
--           ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
--           mock_cache' ← return (mock_cache.log_query () (ys, m) bs),
--           return ((cs, bs), mock_cache')}
--   end }

alias mock_signing_sim_oracle ← mock_signingₛₒ

variables (x₀ pk : X)

-- lemma simulate_mock_signing_sim_oracle_dist_equiv {α : Type}
--   (oa : oracle_comp (hhs_signature G X M n).full_spec α) :
--   dsimulate' (mock_signingₛₒ x₀ pk) oa ≃ₚ
--     dsimulate' ((hhs_signature G X M n).baseₛₒ ∘ₛ
--       (hhs_signature G X M n).signingₛₒ (x₀, pk) (pk -ᵥ x₀)) oa :=
-- begin
--   sorry
-- end

end mock_signing_sim_oracle

-- def mocked_unforgeable_adversary
--   (adv : (hhs_signature G X M n).unforgeable_adversary) :
--   sec_adversary (hhs_signature G X M n).random_spec (X × X)
--     ((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_cache) :=
-- sorry
-- -- { run := λ ks, simulate (mock_signingₛₒ ks.1 ks.2) (adv.run ks) ∅,
-- --   qb := ∅ } -- TODO: bound

-- -- def mocked_adversary_bound (adv : (hhs_signature G X M n).unforgeable_adversary)

-- noncomputable def mock_query_bound (qb : (hhs_signature G X M n).full_spec.query_count) :
--   (hhs_signature G X M n).base_spec.query_count :=
-- { to_fun := λ i, match i with
--     | (sum.inl i) := qb (sum.inl (sum.inl i))
--     | (sum.inr _) := qb (sum.inl (sum.inr ())) ++ qb (sum.inr ())
--   end,
--   active_oracles := sorry,
--   mem_active_oracles_iff' := sorry
-- }

-- def mocked_unforgeable_adversary'
--   (adv : (hhs_signature G X M n).unforgeable_adversary) :
--   sec_adversary (hhs_signature G X M n).base_spec (X × X)
--     ((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_log) :=
-- sorry
-- -- { run := λ ks, simulate (mock_signing_sim_oracle' ks.1 ks.2) (adv.run ks) ∅,
-- --   qb := mock_query_bound adv.qb }

-- noncomputable def mocked_unforgeable_experiment :
--   sec_experiment (hhs_signature G X M n).base_spec unif_spec (X × X)
--     (((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_cache))
--     unit unit unit :=
-- { inp_gen := (($ᵗ X) ×ₘ ($ᵗ X)) ×ₘ (return ()),
--   adv_so := (λ _, (idₛₒ ++ₛ uniformₛₒ).mask_state (equiv.punit_prod unit)),
--   is_valid := begin
--     rintros ⟨⟨x₀, pk⟩, u⟩ ⟨⟨⟨m, zs, hash⟩, mocked_cache⟩, u'⟩,
--     let ys : vector X n := (retrieve_commits x₀ pk zs hash),
--     exact return (mocked_cache.lookup () (ys, m) = some hash)
--   end,
--   exp_so := idₛₒ }

-- noncomputable def mocked_unforgeable_experiment' :
--   sec_experiment (hhs_signature G X M n).base_spec unif_spec (X × X)
--     (((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_log))
--     unit unit unit :=
-- public_experiment (($ᵗ X) ×ₘ ($ᵗ X))
--   (λ _, uniformₛₒ)
--   begin
--     rintros ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, mocked_cache⟩,
--     let ys : vector X n := (retrieve_commits x₀ pk zs hash),
--     exact return (mocked_cache.lookup () (ys, m) = some hash)
--   end idₛₒ
-- -- { inp_gen := (($ᵗ X) ×ₘ ($ᵗ X)) ×ₘ (return ()),
-- --   adv_so := λ _, uniformₛₒ,
-- --   is_valid := begin
-- --     rintros ⟨⟨x₀, pk⟩, u⟩ ⟨⟨⟨m, zs, hash⟩, mocked_cache⟩, u'⟩,
-- --     let ys : vector X n := (retrieve_commits x₀ pk zs hash),
-- --     exact return (mocked_cache.lookup () (ys, m) = some hash)
-- --   end,
-- --   exp_so := idₛₒ }

-- -- theorem le_mocked_advantage (adv : (hhs_signature G X M n).unforgeable_adversary) :
-- --   adv.advantage (hhs_signature G X M n).unforgeable_experiment ≤
-- --     (mocked_unforgeable_adversary adv).advantage mocked_unforgeable_experiment :=
-- -- begin
-- --   sorry
-- -- end

end hhs_signature