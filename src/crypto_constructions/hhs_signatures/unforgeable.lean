/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_constructions.hhs_signatures.mock_signing
import computational_monads.constructions.fork.fork2

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

section fork_reduction

#check indexed_list.map

-- def query_count.transform {spec spec' : oracle_spec}
--   (qc : spec.query_count) (m : spec.ι → spec'.ι) :
--   spec'.query_count :=
-- { to_fun := λ j, of_nat (∑ i in {i : spec.ι | m i = j}, _

-- }

def fork_reduction_query_bound (adv : (hhs_signature G X M n).unforgeable_adv) :
  query_count (unif_spec ++ (unit ↦ₒ vector bool n)) :=
sorry

noncomputable def fork_reduction (adv : (hhs_signature G X M n).unforgeable_adv) :
  fork_adversary (unif_spec ++ (unit ↦ₒ vector bool n))
    (X × X) ((M × vector G n × vector bool n) ×
      (bool × query_log ((vector X n × M) ↦ₒ vector bool n)))
    (sum.inr ()) (adv.run_qb.get_count (sum.inr ())
      + adv.run_qb.get_count (sum.inl (sum.inr ()))) :=
{ run := λ ⟨x₀, pk⟩, begin
    have := simulate (mock_signingₛₒ x₀ pk)
    (adv.run (x₀, pk)) (ff, ∅),
    exact this,
  end,
  run_qb := sorry,
  cf := λ ⟨x₀, pk⟩ ⟨⟨m, zs, bs⟩, ⟨corrupt, cache⟩⟩,
    if corrupt then none else
      let xs := unzip_commits x₀ pk zs bs in
      match cache.lookup () (xs, m) with
      | none := none
      | (some bs') := if bs = bs'
          then some ((cache ()).index_of ((xs, m), bs'))
          else none
      end,
  q_lt_get_count := sorry }

end fork_reduction

section vectorization_reduction

def vectorization_of_fork_result {adv : (hhs_signature G X M n).unforgeable_adv}
  (fr : option (fork_result (fork_reduction adv))) : G :=
begin
  sorry,
end

noncomputable def vectorization_reduction
  (adv : (hhs_signature G X M n).unforgeable_adv) :
  vectorization_adv G X :=
{ run := λ ⟨x₀, pk⟩, simulate' uniformₛₒ
    (vectorization_of_fork_result <$>
      ((fork (fork_reduction adv)).run (x₀, pk))) (),
  run_qb := ∅ }

end vectorization_reduction

end hhs_signature

-- section fork_reduction

-- noncomputable def fork_reduction (adv : (hhs_signature G X M n).unforgeable_adv) :
--   fork_adversary (unif_spec ++ (vector X n × M ↦ₒ vector bool n))
--     (X × X) ((M × vector G n × vector bool n) ×
--       (vector X n × M ↦ₒ vector bool n).query_log)
--     (sum.inr ()) :=
-- { run := λ ⟨x₀, pk⟩, simulate (mock_signingₛₒ x₀ pk)
--     (adv.run (x₀, pk)) ∅,
--   run_qb := mock_signing_qb adv.run_qb,
--   choose_fork := λ ⟨x₀, pk⟩ ⟨⟨m, zs, bs⟩, mock_cache⟩,
--     let xs := unzip_commits x₀ pk zs bs in
--     match mock_cache.lookup () (xs, m) with
--     | (some bs) := some ((mock_cache ()).index_of ((xs, m), bs))
--     | none := none
--     end }

-- lemma le_advantage_fork_reduction (adv : (hhs_signature G X M n).unforgeable_adv) :
--   let inp_gen := (prod.fst <$> (hhs_signature G X M n).keygen ()) in
--   let q : ℕ := (mock_signing_qb adv.run_qb).get_count (sum.inr ()) in
--   (unforgeable_exp adv).advantage * (1 - q / (fintype.card G) ^ n) ^ q ≤
--     sorry := --(fork_reduction adv).advantage inp_gen :=
-- begin
--   simp,
--   sorry
-- end

-- lemma mock_unforgeable_adversary.choose_fork_advantage
--   (adv : (hhs_signature G X M n).unforgeable_adv) :
--   (unforgeable_exp adv).advantage ≤
--     (choose_fork_exp (fork_reduction adv) (prod.mk <$> $ᵗ X <*> $ᵗ X)).advantage :=
-- begin
--   rw [unforgeable_exp.advantage_eq_prob_output],
--   sorry,
-- end

-- noncomputable def vectorization_of_fork_result {adv : (hhs_signature G X M n).unforgeable_adv}
--   (fr : fork_result (fork_reduction adv)) : G :=
-- let rr1 := fr.side_output₁.1 in let rr2 := fr.side_output₂.1 in
--   vec_of_sigs rr2.2 rr1.2

-- section vectorization_of_fork_result

-- variables (adv : (hhs_signature G X M n).unforgeable_adv)

-- -- lemma mocked_cache₁_eq_take_seed₁ (x₀ : X) (pk : X)
-- --   (fr : fork_result (mock_unforgeable_adversary adv))
-- --   (h : fr ∈ ((fork (mock_unforgeable_adversary adv)).run (x₀, pk)).support) :
-- --   ((fr.side_output₁.2 ()).map prod.snd).take fr.1.get_fp =
-- --     (fr.seed₁ (sum.inr ())).take fr.1.get_fp :=
-- -- begin
-- --   rcases fr with ⟨⟨fp₁, ⟨⟨m₁, zs₁, hash₁⟩, mocked_cache₁⟩, seed₁⟩,
-- --     ⟨fp₂, ⟨⟨m₂, zs₂, hash₂⟩, mocked_cache₂⟩, seed₂⟩⟩,
-- --   simp at *,
-- --   sorry,
-- -- end

-- -- lemma take_mocked_cache_eq_take_mocked_cache (x₀ : X) (pk : X)
-- --   (fr : fork_result (fork_reduction adv))
-- --   (h : fr ∈ ((fork (fork_reduction adv)).run (x₀, pk)).support) :
-- --   ((fr.side_output₁.2 ()).map prod.fst).take (fr.1.get_fp + 1) =
-- --     ((fr.side_output₂.2 ()).map prod.fst).take (fr.2.get_fp + 1) :=
-- -- begin
-- --   have := take_queries_seed_eq_take_queries_seed _ _ _ h,
-- --   sorry,
-- -- end

-- lemma vectorization_of_fork_result_eq_vsub (x₀ : X) (pk : X)
--   (fr : fork_result (fork_reduction adv))
--   (h : fr ∈ ((fork (fork_reduction adv)).run (pk, x₀)).support) :
--   fork_success fr → vectorization_of_fork_result fr = pk -ᵥ x₀ :=
-- begin
--   intro hfr,
--   let f_adv := fork_reduction adv,
--   rcases fr with ⟨⟨fp₁, ⟨⟨m₁, zs₁, hash₁⟩, mocked_cache₁⟩, seed₁⟩,
--     ⟨fp₂, ⟨⟨m₂, zs₂, hash₂⟩, mocked_cache₂⟩, seed₂⟩⟩,

--   rw [fork_success_iff_exists] at hfr,
--   obtain ⟨fp, hfp₁, hfp₂, hfp⟩ := hfr,
--   cases hfp₁, cases hfp₂,

--   rw [vectorization_of_fork_result],
--   simp at *,
--   sorry,

--   -- have hcf := fork_point_eq_of_fork_success f_adv _ _ h,
--   -- simp [@eq_comm _ (some fp)] at hcf,
--   -- sorry
--   -- have hcf1 := sorry, --nth_fork_point_eq_unzip_commits hcf.1,
--   -- have hcf2 := sorry, --nth_fork_point_eq_unzip_commits hcf.2,
--   -- clear hcf,

--   -- have h_inp : ((mocked_cache₁ ()).nth fp).map prod.fst = ((mocked_cache₂ ()).nth fp).map prod.fst,
--   -- from sorry,
--   -- have hsm1 : (seed₁ (sum.inr ())).nth fp = ((mocked_cache₁ ()).nth fp).map prod.snd,
--   -- from sorry,
--   -- have hsm2 : (seed₂ (sum.inr ())).nth fp = ((mocked_cache₂ ()).nth fp).map prod.snd,
--   -- from sorry,

--   -- simp only [hcf1, hcf2, option.map_some', prod.mk.inj_iff] at h_inp,
--   -- have h_inp : unzip_commits x₀ pk zs₁ hash₁ = unzip_commits x₀ pk zs₂ hash₂ ∧ m₁ = m₂ := h_inp,

--   -- have h_retrieve : unzip_commits x₀ pk zs₁ hash₁ = unzip_commits x₀ pk zs₂ hash₂ := h_inp.1,
--   -- have h_hash : hash₁ ≠ hash₂,
--   -- by simpa only [value_differs, hsm1, hsm2, hcf1, hcf2, option.map_some', ne.def] using hfp,

--   -- refine vec_of_sigs_eq_vsub x₀ pk n h_hash h_retrieve,
-- end

-- end vectorization_of_fork_result

-- end fork_reduction

-- section vectorization_reduction

-- noncomputable def vectorization_reduction
--   (adv : (hhs_signature G X M n).unforgeable_adv) :
--   vectorization_adv G X :=
-- { run := λ ks, simulate' uniformₛₒ
--     (vectorization_of_fork_result <$>
--       (fork (fork_reduction adv)).run ks) (),
--   run_qb := ∅ }

-- variable (adv : (hhs_signature G X M n).unforgeable_adv)

-- -- lemma prob_output_vsub_vectorization_reduction (x₁ x₂ : X) :
-- --   ⁅= x₁ -ᵥ x₂ | (vectorization_reduction adv).run (x₁, x₂)⁆ =
-- --     (fork_success_exp (mock_unforgeable_adversary adv)).advantage

-- /-- The probability of the fork succeeding is at least the square of
-- the original adversary's success probability, minus a small chance
-- of both oracle calls giving the same result. -/
-- theorem advantage_le_vectorization_advantage :
--   let q := adv.run_qb.get_count (sum.inr ()) + adv.run_qb.get_count (sum.inl (sum.inr ())) in
--   let adv_advantage := (unforgeable_exp adv).advantage in
--   let vec_advantage := (vectorization_exp (vectorization_reduction adv)).advantage in
--   adv_advantage * (adv_advantage / q - (1 / 2 ^ n)) ≤ vec_advantage :=
-- begin
--   have hX : fintype.card X ≠ 0 := fintype.card_ne_zero,
--   let inp_gen := (prod.mk <$> $ᵗ X <*> $ᵗ X),
--   have : (fork_success_exp (fork_reduction adv) inp_gen).advantage ≤
--     (vectorization_exp (vectorization_reduction adv)).advantage,

--   begin
--     simp_rw [vectorization_exp.advantage_eq_tsum, fork_success_exp.advantage_eq_tsum, ennreal.tsum_prod',
--       div_eq_mul_inv, ← ennreal.tsum_mul_right],
--     refine ennreal.tsum_le_tsum (λ x₁, ennreal.tsum_le_tsum (λ x₂, _)),
--     simp only [prob_output_bind_prod_mk, ←pow_two, ennreal.inv_pow, prob_output_coe_sub_spec,
--       prob_output_uniform_select_fintype, prob_event_coe_sort],
--     rw [mul_comm],
--     sorry,
--     -- refine (ennreal.mul_le_mul_right _ _).2 _,
--     -- simp, simp [hX],
--     -- simp only [vectorization_reduction,
--     --   uniform_oracle.prob_output_simulate'],
--     -- rw [← prob_event_singleton_eq_prob_output,
--     --   prob_event_map],
--     -- refine prob_event_mono _ (λ fr hfr, _),
--     -- have := vectorization_of_fork_result_eq_vsub _ x₂ x₁ fr hfr.2 hfr.1,
--     -- simp [this],
--   end,

--   have h' : (unforgeable_exp adv).advantage ≤
--     (choose_fork_exp (fork_reduction adv) inp_gen).advantage,
--   begin
--     apply mock_unforgeable_adversary.choose_fork_advantage,
--   end,

--   refine le_trans _ this,
--   refine le_trans _ (fork_success_exp.choose_fork_advantage_le_fork_success_advantage _ _),
--   simp,
--   sorry,
-- end

-- end vectorization_reduction

-- end hhs_signature