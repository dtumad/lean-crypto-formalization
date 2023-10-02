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
    (some (fin.of_nat (mocked_cache.lookup_index () (ys, m)))) else none

lemma queried_index_eq_some_iff (fp : fin b.succ) :
  let ys : vector X n := (retrieve_commits x₀ pk zs hash) in
  queried_index x₀ pk m zs hash mocked_cache b = some fp ↔
    ((mocked_cache ()).nth fp = some ((ys, m), hash) ∧
      mocked_cache.lookup_index () (ys, m) = fp) :=
begin
  let ys : vector X n := (retrieve_commits x₀ pk zs hash),
  refine ⟨λ h, _, λ h, _⟩,
  {
    by_cases hys : mocked_cache.lookup () (ys, m) = some hash,
    {
      rw [queried_index] at h,
      simp [hys] at h,
      simp [← h],
      sorry,
    },
    {
      sorry,
    }
  },
  {
    sorry,
  }
end

end queried_index

noncomputable def forkable_unforgeable_adversary'
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  fork_adversary (hhs_signature G X M n).base_spec (X × X)
    ((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_log)
    (sum.inr ()) :=
{ choose_fork := begin
    rintros ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, mocked_cache⟩,
    refine queried_index x₀ pk m zs hash mocked_cache _,
  end,
  .. mocked_unforgeable_adversary' adv
}


noncomputable def vectorization_of_fork_result' (x₀ : X) (pk : X)
  {adv : (hhs_signature G X M n).unforgeable_adversary}
  (fr : fork_result (forkable_unforgeable_adversary' adv)) : G :=
let rr1 := fr.side_output₁.1 in let rr2 := fr.side_output₂.1 in
  vectorization_of_zipped_commits rr1.2 rr2.2


noncomputable def forkable_unforgeable_adversary
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  fork_adversary (hhs_signature G X M n).base_spec (X × X)
    (((M × vector G n × vector bool n) × (hhs_signature G X M n).random_spec.query_cache) ×
      (hhs_signature G X M n).base_spec.query_log) (sum.inr ()) :=
fork_adversary.of_choose_input (mocked_unforgeable_adversary adv) (sum.inr ())
  (λ ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, cache⟩, ⟨(retrieve_commits x₀ pk zs hash, m), hash⟩)

section vectorization_of_fork_result

noncomputable def vectorization_of_fork_result (x₀ : X) (pk : X)
  {adv : (hhs_signature G X M n).unforgeable_adversary}
  (fr : fork_result (forkable_unforgeable_adversary adv)) : G :=
let rr1 := fr.side_output₁.1.1 in let rr2 := fr.side_output₂.1.1 in
  vectorization_of_zipped_commits rr1.2 rr2.2

noncomputable def vectorization_of_fork_result'' (x₀ : X) (pk : X)
  {adv : (hhs_signature G X M n).unforgeable_adversary}
  (fr : fork_result (forkable_unforgeable_adversary' adv)) : G :=
vectorization_of_zipped_commits fr.side_output₁.1.2 fr.side_output₂.1.2

-- lemma helper (x₀ : X) (pk : X)
--   (adv : (hhs_signature G X M n).unforgeable_adversary)
--   (fr : fork_result (forkable_unforgeable_adversary' adv)) (hfr : fork_success fr)
--   (h : fr ∈ ((fork' (forkable_unforgeable_adversary' adv)).run (x₀, pk)).support) :
--   _ :=
-- begin

-- end

-- lemma vectorization_of_fork_result_eq_vsub (x₀ : X) (pk : X)
--   (adv : (hhs_signature G X M n).unforgeable_adversary)
--   (fr : fork_result (forkable_unforgeable_adversary adv)) (hfr : fork_success fr)
--   (h : fr ∈ ((fork' (forkable_unforgeable_adversary adv)).run (x₀, pk)).support) :
--   vectorization_of_fork_result x₀ pk fr = pk -ᵥ x₀ :=
-- begin
--   rcases fr with ⟨⟨fp₁, ⟨⟨⟨m₁, zs₁, bs₁⟩, cache₁⟩, log₁⟩, seed₁⟩,
--     ⟨fp₂, ⟨⟨⟨m₂, zs₂, bs₂⟩, cache₂⟩, log₂⟩, seed₂⟩⟩,
--   rw [fork_success_iff_exists] at hfr,
--   obtain ⟨fp, hfp₁, hfp₂, hfp⟩ := hfr,
--   rw [vectorization_of_fork_result],
--   simp at *,
--   -- simp only [fork_result.side_output₁, fork_result.side_output₂],
--   refine vectorization_of_zipped_commits_eq_vsub x₀ pk n _ _,
--   {
--     sorry,
--   },
--   {
--     sorry,
--   }
-- end


lemma vectorization_of_fork_result_eq_vsub' (x₀ : X) (pk : X)
  (adv : (hhs_signature G X M n).unforgeable_adversary)
  (fr : fork_result (forkable_unforgeable_adversary' adv)) (hfr : fork_success fr)
  (h : fr ∈ ((fork' (forkable_unforgeable_adversary' adv)).run (x₀, pk)).support) :
  vectorization_of_fork_result' x₀ pk fr = pk -ᵥ x₀ :=
begin
  let f_adv := forkable_unforgeable_adversary' adv,

  rcases fr with ⟨⟨fp₁, ⟨⟨m₁, zs₁, hash₁⟩, cache₁⟩, seed₁⟩,
    ⟨fp₂, ⟨⟨m₂, zs₂, hash₂⟩, cache₂⟩, seed₂⟩⟩,

  rw [fork_success_iff_exists] at hfr,
  obtain ⟨fp, hfp₁, hfp₂, hfp⟩ := hfr,
  cases hfp₁, cases hfp₂,

  rw [vectorization_of_fork_result'],
  simp at *,

  have hcf := fork_point_eq_of_mem_support_run_fork' f_adv _ _ h,
  simp at hcf,

  -- have hseed := take_to_count_seed_eq_take_to_count_seed f_adv _ _ h,
  -- simp at hseed,

  refine vectorization_of_zipped_commits_eq_vsub x₀ pk n _ _,
  {
    rw [indexed_list.value_differs] at hfp,
    have : (seed₁ (sum.inr ())).nth fp = some hash₁ := begin
      sorry
    end,
    sorry,
  },
  {
    sorry,
  }
end

end vectorization_of_fork_result

noncomputable def vectorization_adversary_of_unforgeable_adversary
  (adv : (hhs_signature G X M n).unforgeable_adversary) :
  vectorization_adversary G X :=
{ run := λ ks, begin
    -- have := fork' (forkable_unforgeable_adversary adv),
    -- have := this.run ks,
    refine dsimulate' uniformₛₒ
      ((λ fr, _) <$> (fork' (forkable_unforgeable_adversary adv)).run ks),
    -- refine (λ fr, _) <$> (fork' (forkable_unforgeable_adversary adv)).run ks,
    have res1 := fr.1.side_output.1.1,
    have res2 := fr.2.side_output.1.1,
    refine vectorization_of_zipped_commits res1.2 res2.2,
  end,
  qb := ∅
}
-- begin
--   have := forkable_unforgeable_adversary adv,
--   have := fork' this,
-- end

-- def mock_signing_fork_adversary (adv : (hhs_signature G X M n).unforgeable_adversary) :
--   fork_adversary (hhs_signature G X M n).base_spec (X × X)
--     ((M × vector (G × bool) n) × (hhs_signature G X M n).random_spec.query_cache
--       × (query_log (hhs_signature G X M n).base_spec))
--     (sum.inr ()) :=
-- begin
--   refine fork_adversary.of_choose_input adv.to_sec_adversary _ _,
-- end

-- -- { run := λ ⟨x₀, pk⟩, mock_simulate_signing_oracle adversary x₀ pk,
-- --   choose_fork := begin
-- --     rintro ⟨x₀, pk⟩ ⟨⟨m, σ⟩, cache⟩,
-- --   end,
-- --   qb := sorry,
-- --   qb_is_bound := sorry,
-- --   q_eq_bound := sorry }

-- -- /-- Fake the signing oracle, and force a query corresponding to adversary's result. -/
-- -- def mock_signing_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary)
-- --   (x₀ pk : X) : oracle_comp (hhs_signature G X M n).base_oracle_spec
-- --     (M × vector (G × bool) n) :=
-- -- do{ ⟨m, σ⟩ ← dsimulate' (idₛₒ ++ₛ mock_signing_sim_oracle x₀ pk) (adversary.run (x₀, pk)),
-- --     query₂ () (retrieve_commits x₀ pk σ, m), -- force a query to the commit for the final output
-- --     return (m, σ) }

-- end mock_signing

-- variable (adversary : (hhs_signature G X M n).unforgeable_adversary)

-- /-- Reduce an unforgeability adversery to a forking adversary that can be passed to
-- `oracle_comp.fork` to get two results, that can be used to construct a adversary for
-- vectorization in the hard homogenous space.
-- `q` is the maximum number of queries made by the adversary to consider. -/
-- def fork_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary) :
--   fork_adversary (hhs_signature G X M n).base_spec (X × X)
--     ((M × vector (G × bool) n) × (query_cache ((vector X n × M) ↦ₒ vector bool n)))
--     sorry sorry :=
-- sorry
-- -- fork_adversary.of_choose_input (λ _ _, sorry) (sum.inr ())
-- --   (λ ⟨x₀, pk⟩ ⟨m, σ⟩, ((retrieve_commits x₀ pk σ, m), σ.map prod.snd))

-- -- lemma advantage_le_forking_reduction_advantage
-- --   (adversary : (hhs_signature G X M n).unforgeable_adversary) (x₀ pk : X) :
-- --     adversary.advantage ≤ (fork_reduction adversary).advantage (x₀, pk) :=
-- -- begin
-- --   sorry
-- -- end

-- /-- If the fork succeeds, we know that there are two valid signatures
-- corresponding to a query with the same input and a different output.
-- This further implies that `retrieve_commits` agrees on both,
-- but the actual booleans are different, which will let us get a vectorization. -/
-- theorem vectorizable_of_fork_success'' (x₀ pk : X)
--   (fr : fork_result (fork_reduction adversary)) (hfr : fork_success fr)
--   (h : fr ∈ (fork (fork_reduction adversary) (x₀, pk)).support) :
--   retrieve_commits x₀ pk fr.side_output₁.1.2 = retrieve_commits x₀ pk fr.side_output₂.1.2
--     ∧ fr.side_output₁.1.2.map prod.snd ≠ fr.side_output₂.1.2.map prod.snd :=
-- begin
--   sorry
-- end

-- /-- The probability of the fork succeeding is at least the square of
-- the original adversary's success probability, minus a small chance
-- of both oracle calls giving the same result. -/
-- theorem le_prob_event_fork_success (x₀ pk : X) :
--   (adversary.advantage ^ 2 / (adversary.qb.get_count (sum.inr (sum.inr ())))) - (1 / 2 ^ n) ≤
--     ⁅fork_success | fork (fork_reduction adversary) (x₀, pk)⁆ :=
-- begin
--   sorry
-- end

-- -- def vectorization_of_commits ()


-- -- /-- If the fork succeeds, we know that there are two valid signatures
-- -- corresponding to a query with the same input and a different output.
-- -- This further implies that `retrieve_commits` agrees on both,
-- -- but the actual booleans are different, which will let us get a vectorization. -/
-- -- theorem vectorizable_of_fork_success (x₀ pk : X)
-- --   (fr : fork_result (fork_reduction adversary)) (hfr : fork_success fr)
-- --   (h : fr ∈ (fork (fork_reduction adversary) (x₀, pk)).support) :
-- --   vectorization_of_fork_result _ x₀ pk fr = pk -ᵥ x₀ :=
-- -- begin
-- --   sorry
-- -- end

-- section vectorization_reduction

-- noncomputable def vectorization_of_fork_result (adv : (hhs_signature G X M n).unforgeable_adversary)
--   (x₀ pk : X) (fr : fork_result (fork_reduction adv)) : G :=
-- begin
--   let σ₁ := fr.side_output₁.1.2,
--   let σ₂ := fr.side_output₂.1.2,
--   let ys₁ := retrieve_commits x₀ pk fr.side_output₁.1.2,
--   let ys₂ := retrieve_commits x₀ pk fr.side_output₂.1.2,
--   let h₁ := fr.side_output₁.1.2.map prod.snd,
--   let h₂ := fr.side_output₂.1.2.map prod.snd,
--   let m : fin n := sorry,
--   exact (σ₁.nth m).1 - (σ₂.nth m).1
-- end

-- variables {spec : oracle_spec} {α β γ : Type }

-- example (f : α → β) (oa : oracle_comp spec α) : f <$> oa = do {x ← oa, return (f x)} := rfl
-- example (og : oracle_comp spec (α → β)) (oa : oracle_comp spec α) :
--   og <*> oa = do {g ← og, x ← oa, return (g x)} := rfl

-- noncomputable def vectorization_reduction (adv : (hhs_signature G X M n).unforgeable_adversary) :
--   vectorization_adversary G X :=
-- { run :=
--   begin
--     rintro ⟨x₀, pk⟩,
--     have := dsimulate' uniformₛₒ (fork (fork_reduction adv) (x₀, pk)),
--     refine vectorization_of_fork_result _ x₀ pk <$> this,
--   end
--   ,
--   qb := sorry,
--   qb_is_bound := sorry,
-- }

-- /-- The probability of the fork succeeding is at least the square of
-- the original adversary's success probability, minus a small chance
-- of both oracle calls giving the same result. -/
-- theorem le_vectorization_advantage (x₀ pk : X) :
--   (adversary.advantage ^ 2 / (adversary.qb.get_count (sum.inr (sum.inr ())))) - (1 / 2 ^ n) ≤
--     (vectorization_reduction adversary).advantage :=
-- begin
--   sorry
-- end

-- end vectorization_reduction

end unforgeable


end hhs_signature