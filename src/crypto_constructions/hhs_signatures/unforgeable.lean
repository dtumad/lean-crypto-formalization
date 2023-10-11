/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_constructions.hhs_signatures.mock_signing
import computational_monads.constructions.fork.of_choose_input

/-!
# Unforgeability of HHS Signature

This file gives an unforgeability proof for `hhs_signature`

-/

namespace hhs_signature

open_locale ennreal big_operators
open oracle_comp oracle_spec algorithmic_homogenous_space hard_homogenous_space
open oracle_spec.indexed_list

variables {G X M : Type} [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}

section unforgeable

section queried_index

variables (x₀ pk : X) (m : M) (zs : vector G n) (hash : vector bool n)
  (mocked_cache : ((vector X n × M) ↦ₒ vector bool n).query_log) (b : ℕ)

/-- Given a valid signature, return the index of the random oracle query for it. -/
def queried_index (x₀ pk : X) (m : M) (zs : vector G n)
  (hash : vector bool n) (mocked_cache : ((vector X n × M) ↦ₒ vector bool n).query_log)
  (b : ℕ) : option (fin b.succ) :=
let ys : vector X n := (retrieve_commits x₀ pk zs hash) in
  if mocked_cache.lookup () (ys, m) = some hash then
    (some (mocked_cache.lookup_index () (ys, m))) else none

lemma nth_fork_point_eq_retrieve_commits {x₀ pk : X} {m : M} {zs : vector G n}
  {hash : vector bool n} {mocked_cache : ((vector X n × M) ↦ₒ vector bool n).query_log}
  {b : ℕ} {fp : fin b.succ}
  (hfp : queried_index x₀ pk m zs hash mocked_cache b = some fp) :
  (mocked_cache ()).nth fp = some ((retrieve_commits x₀ pk zs hash, m), hash) :=
begin
  rw [queried_index] at hfp,
  simp at hfp,
  by_cases h : mocked_cache.lookup () (retrieve_commits x₀ pk zs hash, m) = some hash,
  {
    simp [h] at hfp,
    rw [← hfp],
    simp,
    sorry,
  },
  {
    simp [h] at hfp,
    exact false.elim hfp,
  }
end

-- lemma queried_index_eq_some_iff (fp : fin b.succ) :
--   -- let ys : vector X n := (retrieve_commits x₀ pk zs hash) in
--   queried_index x₀ pk m zs hash mocked_cache b = some fp ↔
--     ((mocked_cache ()).nth fp = some ((retrieve_commits x₀ pk zs hash, m), hash) ∧
--       mocked_cache.lookup_index () (retrieve_commits x₀ pk zs hash, m) = fp) :=
-- begin
--   let ys : vector X n := (retrieve_commits x₀ pk zs hash),
--   refine ⟨λ h, _, λ h, _⟩,
--   {
--     by_cases hys : mocked_cache.lookup () (ys, m) = some hash,
--     {
--       rw [queried_index] at h,
--       simp [hys] at h,
--       simp [← h],
--       sorry,
--     },
--     {
--       sorry,
--     }
--   },
--   {
--     sorry,
--   }
-- end

end queried_index

noncomputable def mock_unforgeable_adversary
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  fork_adversary (hhs_signature G X M n).base_spec (X × X)
    ((M × vector G n × vector bool n) × ((vector X n × M) ↦ₒ vector bool n).query_log)
    (sum.inr ()) :=
{ run := λ ks, simulate (mock_signing_sim_oracle' ks.1 ks.2) (adv.run ks) ∅,
  qb := mock_query_bound adv.qb,
  choose_fork := λ ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, mocked_cache⟩,
    queried_index x₀ pk m zs hash mocked_cache _ }

-- noncomputable def mock_unforgeable_adversary
--   (adv : (hhs_signature G X M n).unforgeable_adversary) :
--   fork_adversary (hhs_signature G X M n).base_spec
--     (X × X)
--     ((M × vector G n × vector bool n) × ((vector X n × M) ↦ₒ vector bool n).query_log)
--     (sum.inr ()) :=
-- { choose_fork := λ ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, mocked_cache⟩,
--     queried_index x₀ pk m zs hash mocked_cache
--       (((mocked_unforgeable_adversary' adv).qb).get_count (sum.inr ())),
--   .. mocked_unforgeable_adversary' adv }

@[simp] lemma choose_fork_eq_queried_index
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  (mock_unforgeable_adversary adv).choose_fork =
    λ ks z, queried_index ks.1 ks.2 z.1.1 z.1.2.1 z.1.2.2 z.2
      ((((mocked_unforgeable_adversary' adv).qb).get_count (sum.inr ()))) :=
begin
  refine funext₂ _,
  rintros ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, mocked_cache⟩,
  refl,
end

noncomputable def vectorization_of_fork_result
  {adv : (hhs_signature G X M n).unforgeable_adversary}
  (fr : fork_result (mock_unforgeable_adversary adv)) : G :=
let rr1 := fr.side_output₁.1 in let rr2 := fr.side_output₂.1 in
  vectorization_of_zipped_commits rr1.2 rr2.2

section vectorization_of_fork_result

variables (adv : (hhs_signature G X M n).unforgeable_adversary)

lemma mocked_cache₁_eq_take_seed₁ (x₀ : X) (pk : X)
  (fr : fork_result (mock_unforgeable_adversary adv))
  (h : fr ∈ ((fork (mock_unforgeable_adversary adv)).run (x₀, pk)).support) :
  ((fr.side_output₁.2 ()).map prod.snd).take fr.1.get_fp =
    (fr.seed₁ (sum.inr ())).take fr.1.get_fp :=
begin
  rcases fr with ⟨⟨fp₁, ⟨⟨m₁, zs₁, hash₁⟩, mocked_cache₁⟩, seed₁⟩,
    ⟨fp₂, ⟨⟨m₂, zs₂, hash₂⟩, mocked_cache₂⟩, seed₂⟩⟩,
  simp at *,
  sorry,
end

lemma take_mocked_cache_eq_take_mocked_cache (x₀ : X) (pk : X)
  (fr : fork_result (mock_unforgeable_adversary adv))
  (h : fr ∈ ((fork (mock_unforgeable_adversary adv)).run (x₀, pk)).support) :
  ((fr.side_output₁.2 ()).map prod.fst).take (fr.1.get_fp + 1) =
    ((fr.side_output₂.2 ()).map prod.fst).take (fr.2.get_fp + 1) :=
begin
  have := take_queries_seed_eq_take_queries_seed _ _ _ h,
  sorry,
end

lemma vectorization_of_fork_result_eq_vsub (x₀ : X) (pk : X)
  (fr : fork_result (mock_unforgeable_adversary adv))
  (h : fr ∈ ((fork (mock_unforgeable_adversary adv)).run (x₀, pk)).support) :
  fork_success fr → vectorization_of_fork_result fr = pk -ᵥ x₀ :=
begin
  intro hfr,
  let f_adv := mock_unforgeable_adversary adv,
  rcases fr with ⟨⟨fp₁, ⟨⟨m₁, zs₁, hash₁⟩, mocked_cache₁⟩, seed₁⟩,
    ⟨fp₂, ⟨⟨m₂, zs₂, hash₂⟩, mocked_cache₂⟩, seed₂⟩⟩,

  rw [fork_success_iff_exists] at hfr,
  obtain ⟨fp, hfp₁, hfp₂, hfp⟩ := hfr,
  cases hfp₁, cases hfp₂,

  rw [vectorization_of_fork_result],
  simp at *,

  have hcf := fork_point_eq_of_mem_support_run_fork f_adv _ _ h,
  simp [@eq_comm _ (some fp)] at hcf,
  have hcf1 := nth_fork_point_eq_retrieve_commits hcf.1,
  have hcf2 := nth_fork_point_eq_retrieve_commits hcf.2,
  clear hcf,

  have h_inp : ((mocked_cache₁ ()).nth fp).map prod.fst = ((mocked_cache₂ ()).nth fp).map prod.fst,
  from sorry,
  have hsm1 : (seed₁ (sum.inr ())).nth fp = ((mocked_cache₁ ()).nth fp).map prod.snd,
  from sorry,
  have hsm2 : (seed₂ (sum.inr ())).nth fp = ((mocked_cache₂ ()).nth fp).map prod.snd,
  from sorry,

  simp only [hcf1, hcf2, option.map_some', prod.mk.inj_iff] at h_inp,
  have h_inp : retrieve_commits x₀ pk zs₁ hash₁ = retrieve_commits x₀ pk zs₂ hash₂ ∧ m₁ = m₂ := h_inp,

  have h_retrieve : retrieve_commits x₀ pk zs₁ hash₁ = retrieve_commits x₀ pk zs₂ hash₂ := h_inp.1,
  have h_hash : hash₁ ≠ hash₂,
  by simpa only [value_differs, hsm1, hsm2, hcf1, hcf2, option.map_some', ne.def] using hfp,

  refine vectorization_of_zipped_commits_eq_vsub x₀ pk n h_hash h_retrieve,
end

end vectorization_of_fork_result

noncomputable def vectorization_reduction
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  vectorization_adversary G X :=
{ run := λ ks, dsimulate' uniformₛₒ
    (vectorization_of_fork_result <$>
      (fork (mock_unforgeable_adversary adv)).run ks),
  qb := ∅ }

variable (adv : (hhs_signature G X M n).unforgeable_adversary)

/-- The probability of the fork succeeding is at least the square of
the original adversary's success probability, minus a small chance
of both oracle calls giving the same result. -/
theorem advantage_le_vectorization_advantage :
  let q := adv.qb.get_count (sum.inr ()) in
  let adv_advantage := adv.advantage (hhs_signature G X M n).unforgeable_experiment in
  let vec_advantage := (vectorization_reduction adv).advantage (vectorization_experiment G X) in
  adv_advantage * (adv_advantage / q - (1 / 2 ^ n)) ≤ vec_advantage :=
begin
  sorry
end

-- end vectorization_reduction

end unforgeable


end hhs_signature