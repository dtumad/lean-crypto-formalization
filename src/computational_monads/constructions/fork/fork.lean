/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging_oracle
import computational_monads.simulation_semantics.constructions.seeded_oracle
import computational_monads.distribution_semantics.option
import crypto_foundations.sec_adversary
import computational_monads.constructions.fork.fork_adversary

/-!
# Forking Computations at a Query
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} {i : spec.ι}

namespace oracle_comp

variable [is_sub_spec uniform_selecting spec]

noncomputable def fork' (adv : fork_adversary spec α β i) :
  sec_adversary spec α (fork_result adv) :=
{ run := λ y,
    do {rr₁ ← adv.seed_and_run y ∅,
      rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i rr₁.get_fp),
      return (rr₁, rr₂)},
  qb := adv.qb + adv.qb }

noncomputable def fork_success_experiment (adv : fork_adversary spec α β i)
  (inp_gen : oracle_comp spec α) : base_sec_experiment spec α (fork_result adv) :=
base_sec_experiment_of_is_valid inp_gen
  (λ x y, return (fork_success y = tt)) uniformₛₒ

noncomputable def fork_advantage (adv : fork_adversary spec α β i)
  (inp_gen : oracle_comp spec α) : ℝ≥0∞ :=
(fork' adv).advantage (fork_success_experiment adv inp_gen)

-- structure forked_adversary (adv : fork_adversary spec α β i q) extends
--   sec_adversary spec α (fork_result adv)

-- noncomputable def fork' (adv : fork_adversary spec α β i q) (y : α) :
--   forked_adversary adv :=
-- { run := λ y, do {
--   rr₁ ← adv.seed_and_run y ∅,
--   rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i rr₁.get_fp),
--   return (rr₁, rr₂)
-- },
--   qb := sorry
-- }

/-- Fork a `fork_adversary` at the point defined by `cf`. -/
noncomputable def fork'' (adv : fork_adversary spec α β i) (y : α) :
  oracle_comp spec (fork_result adv) :=
do {
  rr₁ ← adv.seed_and_run y ∅,
  rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i rr₁.get_fp),
  return (rr₁, rr₂)
}

/-- Fork a `fork_adversary` at the point defined by `cf`. -/
noncomputable def fork (adv : fork_adversary spec α β i) (y : α) :
  oracle_comp spec (fork_result adv) :=
do {
  rr₁ ← adv.seed_and_run y ∅,
  rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i rr₁.get_fp),
  return (rr₁, rr₂)
}

variables (adv : fork_adversary spec α β i) (y : α) (fr : fork_result adv)

/-- Both the resulting `query_seed`s from running `fork` have the same number of seeded values. -/
lemma to_query_count_seed_eq_to_query_count_seed (h : fr ∈ (fork adv y).support) :
  fr.seed₁.to_query_count = fr.seed₂.to_query_count :=
begin
  sorry
end

/-- Up until the forking point, both resulting `query_seed`s have the same seed values. -/
lemma take_queries_seed_eq_take_queries_seed (h : fr ∈ (fork adv y).support) :
  (fr.seed₁.take_at_index i fr.1.get_fp) =
    (fr.seed₂.take_at_index i fr.1.get_fp) :=
begin
  sorry
end

/-- The first side output is in the support of simulating the adversary with the first seed. -/
lemma mem_support_simulate'_seed₁ (h : fr ∈ (fork adv y).support) :
  fr.side_output₁ ∈ (simulate' seededₛₒ (adv.run y) fr.seed₁).support :=
begin
  sorry,
end

/-- The second side output is in the support of simulating the adversary with the second seed. -/
lemma mem_support_simulate'_seed₂ (h : fr ∈ (fork adv y).support) :
  fr.side_output₂ ∈ (simulate' seededₛₒ (adv.run y) fr.seed₂).support :=
begin
  sorry,
end

/-- If `fork` returns success then both runs chose the same fork value. -/
lemma choose_fork_eq_of_fork_success (h : fr ∈ (fork adv y).support) :
  adv.choose_fork y fr.side_output₁ = fr.fork_point₁ ∧
    adv.choose_fork y fr.side_output₂ = fr.fork_point₂ :=
begin
  sorry
end

/-- If `fork` returns success then the adversary must have thrown away at least one value. -/
lemma choose_fork_ne_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  fr.fork_point₁ ≠ some adv.q :=
begin
  sorry
end

/-- If `fork` returns success then the output after the forking point
TODO: this should have a small chance to fail instead. -/
lemma seed_differs_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  (fr.seed₁ i).nth (fr.1.get_fp) ≠
    (fr.seed₂ i).nth (fr.2.get_fp) :=
begin
  sorry
end

section prob_event_fork_success

/-- The set of all possible shared seeds for the two runs of the computation. -/
noncomputable def poss_shared_seeds (qc : query_count spec)
  (i : spec.ι) {q : ℕ} (fp : fin q.succ) : finset (query_seed spec) :=
(generate_seed (qc.decrement i fp)).fin_support

/-- -/
lemma le_prob_output_fork_points (adv : fork_adversary spec α β i) (fp : fin adv.q.succ) :
  ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2 ≤
    ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
      rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i fp),
      return (rr₁.fork_point, rr₂.fork_point)}⁆ :=
calc ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2
  -- Generate the eventual shared portion of the seed beforehand.
  = ⁅= some fp | do {shared_seed ← ↑(generate_seed (adv.shared_query_count fp)),
      run_result.fork_point <$> adv.seed_and_run y shared_seed}⁆ ^ 2 :
    begin
      rw [← fork_adversary.prob_output_fork_point_map_seed_and_run],
      have : adv.shared_query_count fp ≤ adv.qb := indexed_list.take_at_index_le _ _ _,
      refine congr_arg (λ z : ℝ≥0∞, z ^ 2) _,
      rw_dist_equiv [(fork_adversary.generate_seed_bind_seed_and_run_dist_equiv adv y _ this).symm],
      rw_dist_equiv [map_bind_dist_equiv],
    end
  -- Sum over the possible values of the shared portion of the seed.
  ... = (∑ shared_seed in (generate_seed (adv.shared_query_count fp)).fin_support,
          ⁅= shared_seed | generate_seed (adv.shared_query_count fp)⁆ *
            ⁅= some fp | run_result.fork_point <$> adv.seed_and_run y shared_seed⁆) ^ 2 :
    congr_arg (λ z : ℝ≥0∞, z ^ 2) (by simp_rw [prob_output_bind_eq_sum_fin_support,
      fin_support_coe_sub_spec, prob_output_coe_sub_spec])
  -- Apply Jensen's inequality to the sum over shared seed values.
  ... ≤ ∑ shared_seed in (generate_seed (adv.shared_query_count fp)).fin_support,
          ⁅= shared_seed | generate_seed (adv.shared_query_count fp)⁆ *
            ⁅= some fp | run_result.fork_point <$> adv.seed_and_run y shared_seed⁆ ^ 2 :
    begin
      refine le_trans (ennreal.pow_two_sum_le_sum_pow_two _ _ ((λ _ _, ennreal.mul_ne_top
        (prob_output_ne_top _ _) (prob_output_ne_top _ _)))) _,
      refine le_of_eq (finset.sum_congr rfl (λ shared_seed hss, _)),
      have hsfp := (coe_query_count_of_mem_fin_support_generate_seed hss),
      rw [mul_pow, prob_output_generate_seed _ _ hsfp, card_fin_support_generate_seed, pow_two,
        ← mul_assoc, ← mul_assoc, ennreal.mul_inv_cancel (nat.cast_ne_zero.2
        (possible_outcomes_ne_zero _)) (ennreal.nat_ne_top _), one_mul]
    end
  -- Combine the two seperate runs of the adversary into one computation.
  ... = ∑ shared_seed in (generate_seed (adv.shared_query_count fp)).fin_support,
    ⁅= shared_seed | generate_seed (adv.shared_query_count fp)⁆ *
      ⁅= (some fp, some fp) | do {
        rr₁ ← adv.seed_and_run y shared_seed,
        rr₂ ← adv.seed_and_run y shared_seed,
        return (rr₁.fork_point, rr₂.fork_point)
      }⁆ :
    begin
      refine finset.sum_congr rfl (λ shared_seed _, congr_arg (λ z : ℝ≥0∞, _ * z) _),
      rw [pow_two],
      refine trans (symm (prob_output_mprod _ _ (some fp, some fp))) _,
      rw_dist_equiv [bind_map_dist_equiv _ _ run_result.fork_point,
        bind_map_dist_equiv _ _ run_result.fork_point]
    end
  -- Reduce the shared seed generation back inside the main computation.
  ... = ⁅= (some fp, some fp) | do {shared_seed ← ↑(generate_seed (adv.shared_query_count fp)),
          rr₁ ← adv.seed_and_run y shared_seed,
          rr₂ ← adv.seed_and_run y shared_seed,
          return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    begin
      rw [prob_output_bind_eq_sum_fin_support],
      simp_rw [fin_support_coe_sub_spec, prob_output_coe_sub_spec],
    end
  ... = ⁅= (some fp, some fp) | do {shared_seed ← ↑(generate_seed (adv.shared_query_count fp)),
          rr₁ ← adv.seed_and_run y shared_seed,
          rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i fp),
          return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    begin
      pairwise_dist_equiv with shared_seed hss rr hrr,
      suffices : shared_seed = indexed_list.take_at_index rr.seed i ↑fp,
      by rw [this],
      rw ← fork_adversary.shared_seed_of_mem_support_seed_and_run adv y shared_seed rr hrr,
      rw [support_coe_sub_spec] at hss,
      rw [coe_query_count_of_mem_support_generate_seed hss],
      rw [← indexed_list.take_to_count_take_at_index],
      rw [fork_adversary.shared_query_count, indexed_list.coe_query_count_eq,
        indexed_list.to_query_count_take_at_index],
      rw [adv.to_query_count_of_mem_support_seed_and_run _ _ _ hrr],
      rw [coe_query_count_of_mem_support_generate_seed hss],
      refine indexed_list.take_at_index_le _ _ _,
    end
  ... = ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
          rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i fp),
          return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    begin
      by_dist_equiv,
      have := adv.generate_seed_bind_seed_and_run_dist_equiv y (adv.shared_query_count fp)
        (indexed_list.take_at_index_le _ _ _),
      rw_dist_equiv [this.symm, bind_bind_dist_equiv_assoc]
    end

/--  -/
lemma le_prob_event_same_fork_point (adv : fork_adversary spec α β i) :
  adv.cf_advantage y ^ 2 / adv.q.succ ≤ ⁅same_fork_point | fork adv y⁆ :=
calc adv.cf_advantage y ^ 2 / adv.q.succ
    = ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / adv.q.succ : sorry
  -- Rewrite the probability of not getting `none` as the sum of each `some` possibility.
  ... = (∑ fp, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆) ^ 2 / adv.q.succ :
    by rw [prob_event_ne_none_eq_sum]
  -- Apply Jensen's inequality and cancel out the factor of `q.succ`.
  ... ≤ ∑ fp, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2 :
    le_trans (le_of_eq (by rw [one_add_one_eq_two, pow_one, ← fintype.card, fintype.card_fin]))
      (ennreal.pow_sum_div_card_le_sum_pow _ _ (λ _ _, prob_output_ne_top _ _) 1)
  -- Apply `le_prob_output_fork_points` to the inner probability calculation.
  ... ≤ ∑ fp, ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
            rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i ↑fp),
            return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    finset.sum_le_sum (λ fp hfp, by apply le_prob_output_fork_points)
  ... = ∑ fp, ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
            rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i (rr₁.fork_point.get_or_else 0)),
            return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    begin
      refine finset.sum_congr rfl (λ fp _, _),
      simp only [prob_output_bind_eq_tsum],
      refine tsum_congr (λ rr₁, _),
      refine congr_arg (λ z : ℝ≥0∞, _ * z) _,
      refine tsum_congr (λ rr₂, _),
      by_cases h : some fp = rr₁.fork_point,
      { rw [← h, option.get_or_else_some] },
      { have : (some fp, some fp) ≠ (rr₁.fork_point, rr₂.fork_point),
        by simp [prod.eq_iff_fst_eq_snd_eq, h],
        simp_rw [prob_output_return_of_ne _ this, mul_zero] }
    end
  -- Replace the sum over possible outputs with the chances of fork success
  ... ≤ ⁅same_fork_point | fork adv y⁆ :
    begin
      rw [prob_event_same_fork_point],
      refine le_of_eq (finset.sum_congr rfl (λ fp _, _)),
      rw_dist_equiv [map_bind_dist_equiv _ _ fork_result.fork_points],
      pairwise_dist_equiv_deep,
    end


theorem prob_event_fork_success (adv : fork_adversary spec α β i) :
  adv.cf_advantage y * (adv.cf_advantage y / adv.q - (fintype.card (spec.range i))⁻¹) ≤
    ⁅λ z, fork_success z = tt | fork adv y⁆ :=
begin
  sorry
end


end prob_event_fork_success

end oracle_comp