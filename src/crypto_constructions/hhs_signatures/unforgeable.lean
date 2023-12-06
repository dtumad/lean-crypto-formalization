/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_constructions.hhs_signatures.mock_signing
import computational_monads.constructions.fork.fork

/-!
# Unforgeability of HHS Signature

This file gives an unforgeability proof for `hhs_signature`

-/

namespace hhs_signature

open_locale ennreal big_operators
open oracle_comp oracle_spec algorithmic_homogenous_space hard_homogenous_space
open oracle_spec.indexed_list signature_alg

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
    (some ((mocked_cache ()).index_of ((ys, m), hash))) else none

lemma nth_fork_point_eq_retrieve_commits {x₀ pk : X} {m : M} {zs : vector G n}
  {hash : vector bool n} {mocked_cache : ((vector X n × M) ↦ₒ vector bool n).query_log}
  {b : ℕ} {fp : fin b.succ}
  (hfp : queried_index x₀ pk m zs hash mocked_cache b = some fp) :
  (mocked_cache ()).nth fp = some ((retrieve_commits x₀ pk zs hash, m), hash) :=
begin
  sorry,
  -- rw [queried_index] at hfp,
  -- simp at hfp,
  -- by_cases h : mocked_cache.lookup () (retrieve_commits x₀ pk zs hash, m) = some hash,
  -- {
  --   simp [h] at hfp,
  --   rw [← hfp],
  --   simp,
  --   sorry,
  -- },
  -- {
  --   simp [h] at hfp,
  --   exact false.elim hfp,
  -- }
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

def mock_adversary_qb (adv : (hhs_signature G X M n).unforgeable_adv) :
  (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n)).query_count :=
{ to_fun := λ i, match i with
  | (sum.inl i) := adv.run_qb (sum.inl (sum.inl i))
  | (sum.inr ()) := adv.run_qb (sum.inl (sum.inr ())) ++ adv.run_qb (sum.inr ())
  end,
  active_oracles := adv.run_qb.active_oracles.image (λ i, match i with
  | (sum.inl i) := i
  | (sum.inr ()) := sum.inr ()
  end),
  mem_active_oracles_iff' := λ i,
  begin
    sorry,
  end }

noncomputable def mock_unforgeable_adversary
  (adv : (hhs_signature G X M n).unforgeable_adv) :
  fork_adversary (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
    (X × X)
    ((M × vector G n × vector bool n) × ((vector X n × M) ↦ₒ vector bool n).query_log)
    (sum.inr ()) :=
{ run := λ ks, simulate (mock_signing_sim_oracle ks.1 ks.2) (adv.run ks) ∅,
  run_qb := mock_adversary_qb adv,
  choose_fork := λ ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, mocked_cache⟩,
    queried_index x₀ pk m zs hash mocked_cache _ }

lemma mock_unforgeable_adversary.choose_fork_advantage
  (adv : (hhs_signature G X M n).unforgeable_adv) :
  (unforgeable_exp adv).advantage ≤
    (choose_fork_exp (mock_unforgeable_adversary adv) (($ᵗ X) ×ₘ ($ᵗ X))).advantage :=
begin
  rw [unforgeable_exp.advantage_eq_prob_output],
  sorry,
end

-- @[simp] lemma choose_fork_eq_queried_index
--   (adv : (hhs_signature G X M n).unforgeable_adversary) :
--   (mock_unforgeable_adversary adv).choose_fork =
--     λ ks z, queried_index ks.1 ks.2 z.1.1 z.1.2.1 z.1.2.2 z.2
--       ((((mocked_unforgeable_adversary' adv).qb).get_count (sum.inr ()))) :=
-- begin
--   refine funext₂ _,
--   rintros ⟨x₀, pk⟩ ⟨⟨m, zs, hash⟩, mocked_cache⟩,
--   refl,
-- end

noncomputable def vectorization_of_fork_result {adv : (hhs_signature G X M n).unforgeable_adv}
  (fr : fork_result (mock_unforgeable_adversary adv)) : G :=
let rr1 := fr.side_output₁.1 in let rr2 := fr.side_output₂.1 in
  vectorization_of_zipped_commits rr2.2 rr1.2

section vectorization_of_fork_result

variables (adv : (hhs_signature G X M n).unforgeable_adv)

-- lemma mocked_cache₁_eq_take_seed₁ (x₀ : X) (pk : X)
--   (fr : fork_result (mock_unforgeable_adversary adv))
--   (h : fr ∈ ((fork (mock_unforgeable_adversary adv)).run (x₀, pk)).support) :
--   ((fr.side_output₁.2 ()).map prod.snd).take fr.1.get_fp =
--     (fr.seed₁ (sum.inr ())).take fr.1.get_fp :=
-- begin
--   rcases fr with ⟨⟨fp₁, ⟨⟨m₁, zs₁, hash₁⟩, mocked_cache₁⟩, seed₁⟩,
--     ⟨fp₂, ⟨⟨m₂, zs₂, hash₂⟩, mocked_cache₂⟩, seed₂⟩⟩,
--   simp at *,
--   sorry,
-- end

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
  (h : fr ∈ ((fork (mock_unforgeable_adversary adv)).run (pk, x₀)).support) :
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
  sorry
  -- have hcf1 := sorry, --nth_fork_point_eq_retrieve_commits hcf.1,
  -- have hcf2 := sorry, --nth_fork_point_eq_retrieve_commits hcf.2,
  -- clear hcf,

  -- have h_inp : ((mocked_cache₁ ()).nth fp).map prod.fst = ((mocked_cache₂ ()).nth fp).map prod.fst,
  -- from sorry,
  -- have hsm1 : (seed₁ (sum.inr ())).nth fp = ((mocked_cache₁ ()).nth fp).map prod.snd,
  -- from sorry,
  -- have hsm2 : (seed₂ (sum.inr ())).nth fp = ((mocked_cache₂ ()).nth fp).map prod.snd,
  -- from sorry,

  -- simp only [hcf1, hcf2, option.map_some', prod.mk.inj_iff] at h_inp,
  -- have h_inp : retrieve_commits x₀ pk zs₁ hash₁ = retrieve_commits x₀ pk zs₂ hash₂ ∧ m₁ = m₂ := h_inp,

  -- have h_retrieve : retrieve_commits x₀ pk zs₁ hash₁ = retrieve_commits x₀ pk zs₂ hash₂ := h_inp.1,
  -- have h_hash : hash₁ ≠ hash₂,
  -- by simpa only [value_differs, hsm1, hsm2, hcf1, hcf2, option.map_some', ne.def] using hfp,

  -- refine vectorization_of_zipped_commits_eq_vsub x₀ pk n h_hash h_retrieve,
end

end vectorization_of_fork_result

noncomputable def vectorization_reduction
  (adv : (hhs_signature G X M n).unforgeable_adv) :
  vectorization_adv G X :=
{ run := λ ks, simulate' uniformₛₒ
    (vectorization_of_fork_result <$>
      (fork (mock_unforgeable_adversary adv)).run ks) (),
  run_qb := ∅ }

variable (adv : (hhs_signature G X M n).unforgeable_adv)

-- lemma prob_output_vsub_vectorization_reduction (x₁ x₂ : X) :
--   ⁅= x₁ -ᵥ x₂ | (vectorization_reduction adv).run (x₁, x₂)⁆ =
--     (fork_success_exp (mock_unforgeable_adversary adv)).advantage

/-- The probability of the fork succeeding is at least the square of
the original adversary's success probability, minus a small chance
of both oracle calls giving the same result. -/
theorem advantage_le_vectorization_advantage :
  let q := adv.run_qb.get_count (sum.inr ()) + adv.run_qb.get_count (sum.inl (sum.inr ())) in
  let adv_advantage := (unforgeable_exp adv).advantage in
  let vec_advantage := (vectorization_exp (vectorization_reduction adv)).advantage in
  adv_advantage * (adv_advantage / q - (1 / 2 ^ n)) ≤ vec_advantage :=
begin
  have hX : fintype.card X ≠ 0 := fintype.card_ne_zero,
  let inp_gen := do {x₁ ←$ᵗ X, x₂ ←$ᵗ X, return (x₁, x₂)},
  have : (fork_success_exp (mock_unforgeable_adversary adv) inp_gen).advantage ≤
    (vectorization_exp (vectorization_reduction adv)).advantage,

  begin
    simp_rw [vectorization_exp.advantage_eq_tsum, fork_success_exp.advantage_eq_tsum, ennreal.tsum_prod',
      div_eq_mul_inv, ← ennreal.tsum_mul_right],
    refine ennreal.tsum_le_tsum (λ x₁, ennreal.tsum_le_tsum (λ x₂, _)),
    simp only [prob_output_bind_prod_mk, ←pow_two, ennreal.inv_pow, prob_output_coe_sub_spec,
      prob_output_uniform_select_fintype, prob_event_coe_sort],
    rw [mul_comm],
    refine (ennreal.mul_le_mul_right _ _).2 _,
    simp, simp [hX],
    simp only [vectorization_reduction,
      uniform_oracle.prob_output_simulate'],
    rw [← prob_event_singleton_eq_prob_output,
      prob_event_map],
    refine prob_event_mono _ (λ fr hfr, _),
    have := vectorization_of_fork_result_eq_vsub _ x₂ x₁ fr hfr.2 hfr.1,
    simp [this],
  end,

  have h' : (unforgeable_exp adv).advantage ≤
    (choose_fork_exp (mock_unforgeable_adversary adv) inp_gen).advantage,
  begin
    apply mock_unforgeable_adversary.choose_fork_advantage,
  end,

  refine le_trans _ this,
  refine le_trans _ (le_fork_advantage _ _),
  simp,
  sorry,
end

-- end vectorization_reduction

end unforgeable


end hhs_signature