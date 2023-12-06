/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging_oracle
import computational_monads.simulation_semantics.constructions.seeded_oracle
import computational_monads.distribution_semantics.option
import computational_monads.constructions.fork.fork_adversary

/-!
# Forking Computations at a Query
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec fintype

variables {α β γ : Type} {spec spec' : oracle_spec} {i : spec.ι}

namespace oracle_comp

-- TODO!!!: weird
variable [is_sub_spec unif_spec spec]

noncomputable def fork (adv : fork_adversary spec α β i) :
  sec_adv spec α (fork_result adv) :=
{ run := λ x,
    do {rr₁ ← adv.seed_and_run x ∅,
      rr₂ ← adv.seed_and_run x (rr₁.seed.take_at_index i rr₁.get_fp),
      return (rr₁, rr₂)},
  run_qb := 2 • adv.run_qb }

noncomputable def fork_success_exp (adv : fork_adversary spec α β i)
  (inp_gen : oracle_comp spec α) : sec_exp spec α (fork_result adv) :=
{ inp_gen := inp_gen,
  main := (fork adv).run,
  is_valid := λ x fr, fork_success fr,
  base_sim_oracle := uniformₛₒ, init_state := (), .. }

namespace fork_success_exp

variables (adv : fork_adversary spec α β i)
  (inp_gen : oracle_comp spec α)

@[simp] lemma inp_gen_eq : (fork_success_exp adv inp_gen).inp_gen = inp_gen := rfl

@[simp] lemma main_eq : (fork_success_exp adv inp_gen).main = (fork adv).run := rfl

@[simp] lemma is_valid_eq : (fork_success_exp adv inp_gen).is_valid =
  λ x fr, fork_success fr := rfl

@[simp] lemma base_S_eq : (fork_success_exp adv inp_gen).base_S = unit := rfl

@[simp] lemma base_sim_oracle_eq : (fork_success_exp adv inp_gen).base_sim_oracle =
  uniformₛₒ := rfl

@[simp] lemma run_eq : (fork_success_exp adv inp_gen).run =
  simulate' uniformₛₒ (do {x ← inp_gen, y ← (fork adv).run x, return (x, y)}) () := rfl

lemma advantage_eq_tsum : (fork_success_exp adv inp_gen).advantage =
  ∑' x, ⁅= x | inp_gen⁆ * ⁅λ fr, fork_success fr | (fork adv).run x⁆ :=
begin
  rw [sec_exp.advantage, run_eq, uniform_oracle.prob_event_simulate', prob_event_bind_eq_tsum],
  simpa only [prob_event_bind_return],
end

end fork_success_exp

-- noncomputable def fork_success_experiment (adv : fork_adversary spec α β i)
--   (inp_gen : oracle_comp spec α) :
--   sec_experiment spec spec α (fork_result adv) unit unit unit :=
-- public_experiment inp_gen (λ x, idₛₒ)
--   (λ x fr, return (fork_success fr)) uniformₛₒ

-- noncomputable def fork_advantage (adv : fork_adversary spec α β i)
--   (inp_gen : oracle_comp spec α) : ℝ≥0∞ :=
-- (fork adv).advantage (fork_success_experiment adv inp_gen)

-- noncomputable def fork_advantage' (adv : fork_adversary spec α β i)
--   (inp_gen : prob_comp spec α) : ℝ≥0∞ :=
-- ⁅λ fr, fork_success fr = tt | inp_gen >>= (fork adv).run⁆

variables (adv : fork_adversary spec α β i) (y : α) (fr : fork_result adv)

lemma support_run_fork (adv : fork_adversary spec α β i) (x : α) :
  ((fork adv).run x).support = {fr | fr.1 ∈ (adv.seed_and_run x ∅).support ∧
    fr.2 ∈ (adv.seed_and_run x (fr.1.seed.take_at_index i fr.1.get_fp)).support} :=
begin
  simp only [fork],
  rw [support_bind_bind_prod_mk],
  refl,
end

section fork_point

lemma fork_point_eq_of_mem_support_run_fork (adv : fork_adversary spec α β i)
  (fr : fork_result adv) (x : α) (h : fr ∈ ((fork adv).run x).support) :
  fr.fork_point₁ = adv.choose_fork x fr.side_output₁ ∧
    fr.fork_point₂ = adv.choose_fork x fr.side_output₂ :=
begin
  simp only [support_run_fork, set.mem_set_of_eq] at h,
  refine ⟨adv.fork_point_eq_choose_fork x ∅ fr.1 h.1,
    adv.fork_point_eq_choose_fork x _ fr.2 h.2⟩,
end

/-- If `fork` returns success then both runs chose the same fork value. -/
lemma choose_fork_eq_of_fork_success (h : fr ∈ ((fork adv).run y).support)
  (hfr : fork_success fr) :
  adv.choose_fork y fr.side_output₁ = adv.choose_fork y fr.side_output₂ :=
begin
  sorry
end

lemma fork_point_eq_of_fork_success (h : fr ∈ ((fork adv).run y).support)
  (hfr : fork_success fr) : fr.fork_point₁ = fr.fork_point₂ :=
begin
  sorry
end

end fork_point

lemma take_to_count_seed_eq_take_at_index_seed (adv : fork_adversary spec α β i)
  (fr : fork_result adv) (x : α) (h : fr ∈ ((fork adv).run x).support) :
  fr.seed₂.take_to_count (fr.seed₁.take_at_index i fr.1.get_fp) =
    fr.seed₁.take_at_index i fr.1.get_fp :=
begin
  simp only [support_run_fork, set.mem_set_of_eq] at h,
  exact adv.take_to_count_seed_eq_seed x _ _ h.2,
end

/-- Both the resulting `query_seed`s from running `fork` have the same number of seeded values. -/
lemma to_query_count_seed_eq_to_query_count_seed (h : fr ∈ ((fork adv).run y).support) :
  fr.seed₁.to_query_count = fr.seed₂.to_query_count :=
begin
  sorry
end

/-- Up until the forking point, both resulting `query_seed`s have the same seed values. -/
lemma take_queries_seed_eq_take_queries_seed (h : fr ∈ ((fork adv).run y).support) :
  (fr.seed₁.take_at_index i fr.1.get_fp) =
    (fr.seed₂.take_at_index i fr.1.get_fp) :=
begin
  sorry
end

section side_output

/-- The first side output is in the support of simulating the adversary with the first seed. -/
lemma mem_support_simulate'_seed₁ (h : fr ∈ ((fork adv).run y).support) :
  fr.side_output₁ ∈ (simulate' seededₛₒ (adv.run y) fr.seed₁).support :=
begin
  sorry,
end

/-- The second side output is in the support of simulating the adversary with the second seed. -/
lemma mem_support_simulate'_seed₂ (h : fr ∈ ((fork adv).run y).support) :
  fr.side_output₂ ∈ (simulate' seededₛₒ (adv.run y) fr.seed₂).support :=
begin
  sorry,
end

end side_output

/-- If `fork` returns success then the adversary must have thrown away at least one value. -/
lemma choose_fork_ne_max_of_fork_success (h : fr ∈ ((fork adv).run y).support)
  (hfr : fork_success fr) : fr.fork_point₁ ≠ some adv.q :=
begin
  sorry
end

/-- If `fork` returns success then the output after the forking point
TODO: this should have a small chance to fail instead. -/
lemma seed_differs_of_fork_success (h : fr ∈ ((fork adv).run y).support) (hfr : fork_success fr) :
  (fr.seed₁ i).nth (fr.1.get_fp) ≠ (fr.seed₂ i).nth (fr.2.get_fp) :=
begin
  rw [fork_success_iff_exists] at hfr,
  obtain ⟨fp, hfp₁, hfp₂, hfp⟩ := hfr,
  have h1 : fr.1.get_fp = fp,
  from symm (trans (option.get_or_else_some fp 0).symm (congr_fun (congr_arg _ hfp₁) 0).symm),
  have h2 : fr.2.get_fp = fp,
  from symm (trans (option.get_or_else_some fp 0).symm (congr_fun (congr_arg _ hfp₂) 0).symm),
  simp only [h1, h2, fork_result.seed₁, fork_result.seed₂, ne.def],
  exact hfp,
end

section prob_event_fork_success

-- /-- The set of all possible shared seeds for the two runs of the computation. -/
-- noncomputable def poss_shared_seeds (qc : query_count spec)
--   (i : spec.ι) {q : ℕ} (fp : fin q.succ) : finset (query_seed spec) :=
-- (generate_seed (qc.decrement i fp)).fin_support

/-- -/
lemma le_prob_output_fork_points (adv : fork_adversary spec α β i) (fp : fin adv.q.succ) :
  ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2 ≤
    ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
      rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index i fp),
      return (rr₁.fork_point, rr₂.fork_point)}⁆ :=
sorry
-- calc ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2
--   -- Generate the eventual shared portion of the seed beforehand.
--   = ⁅= some fp | do {shared_seed ← ↑(generate_seed (adv.shared_query_count fp)),
--       run_result.fork_point <$> adv.seed_and_run y shared_seed}⁆ ^ 2 :
--     begin
--       rw [← fork_adversary.prob_output_fork_point_map_seed_and_run],
--       have : adv.shared_query_count fp ≤ adv.qb := indexed_list.take_at_index_le _ _ _,
--       refine congr_arg (λ z : ℝ≥0∞, z ^ 2) _,
--       rw_dist_equiv [(fork_adversary.generate_seed_bind_seed_and_run_dist_equiv adv y _ this).symm],
--       rw_dist_equiv [map_bind_dist_equiv],
--     end
--   -- Sum over the possible values of the shared portion of the seed.
--   ... = (∑ shared_seed in (generate_seed (adv.shared_query_count fp)).fin_support,
--           ⁅= shared_seed | generate_seed (adv.shared_query_count fp)⁆ *
--             ⁅= some fp | run_result.fork_point <$> adv.seed_and_run y shared_seed⁆) ^ 2 :
--     congr_arg (λ z : ℝ≥0∞, z ^ 2) (by simp_rw [prob_output_bind_eq_sum_fin_support,
--       fin_support_coe_sub_spec, prob_output_coe_sub_spec])
--   -- Apply Jensen's inequality to the sum over shared seed values.
--   ... ≤ ∑ shared_seed in (generate_seed (adv.shared_query_count fp)).fin_support,
--           ⁅= shared_seed | generate_seed (adv.shared_query_count fp)⁆ *
--             ⁅= some fp | run_result.fork_point <$> adv.seed_and_run y shared_seed⁆ ^ 2 :
--     begin
--       refine le_trans (ennreal.pow_two_sum_le_sum_pow_two _ _ ((λ _ _, ennreal.mul_ne_top
--         (prob_output_ne_top _ _) (prob_output_ne_top _ _)))) _,
--       refine le_of_eq (finset.sum_congr rfl (λ shared_seed hss, _)),
--       have hsfp := (coe_query_count_of_mem_fin_support_generate_seed hss),
--       rw [mul_pow, prob_output_generate_seed _ _ hsfp, card_fin_support_generate_seed, pow_two,
--         ← mul_assoc, ← mul_assoc, ennreal.mul_inv_cancel (nat.cast_ne_zero.2
--         (possible_outcomes_ne_zero _)) (ennreal.nat_ne_top _), one_mul]
--     end
--   -- Combine the two seperate runs of the adversary into one computation.
--   ... = ∑ shared_seed in (generate_seed (adv.shared_query_count fp)).fin_support,
--     ⁅= shared_seed | generate_seed (adv.shared_query_count fp)⁆ *
--       ⁅= (some fp, some fp) | do {
--         rr₁ ← adv.seed_and_run y shared_seed,
--         rr₂ ← adv.seed_and_run y shared_seed,
--         return (rr₁.fork_point, rr₂.fork_point)
--       }⁆ :
--     begin
--       refine finset.sum_congr rfl (λ shared_seed _, congr_arg (λ z : ℝ≥0∞, _ * z) _),
--       rw [pow_two],
--       refine trans (symm (prob_output_mprod _ _ (some fp, some fp))) _,
--       rw_dist_equiv [bind_map_dist_equiv _ _ run_result.fork_point,
--         bind_map_dist_equiv _ _ run_result.fork_point]
--     end
--   -- Reduce the shared seed generation back inside the main computation.
--   ... = ⁅= (some fp, some fp) | do {shared_seed ← ↑(generate_seed (adv.shared_query_count fp)),
--           rr₁ ← adv.seed_and_run y shared_seed,
--           rr₂ ← adv.seed_and_run y shared_seed,
--           return (rr₁.fork_point, rr₂.fork_point)}⁆ :
--     begin
--       rw [prob_output_bind_eq_sum_fin_support],
--       simp_rw [fin_support_coe_sub_spec, prob_output_coe_sub_spec],
--     end
--   ... = ⁅= (some fp, some fp) | do {shared_seed ← ↑(generate_seed (adv.shared_query_count fp)),
--           rr₁ ← adv.seed_and_run y shared_seed,
--           rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) fp),
--           return (rr₁.fork_point, rr₂.fork_point)}⁆ :
--     begin
--       pairwise_dist_equiv with shared_seed hss rr hrr,
--       suffices : shared_seed = indexed_list.take_at_index rr.seed (sum.inr i) ↑fp,
--       by rw [this],
--       rw ← fork_adversary.take_to_count_seed_eq_seed adv y shared_seed rr hrr,
--       rw [support_coe_sub_spec] at hss,
--       rw [coe_query_count_of_mem_support_generate_seed hss],
--       rw [← indexed_list.take_to_count_take_at_index],
--       rw [fork_adversary.shared_query_count, indexed_list.coe_query_count_eq,
--         indexed_list.to_query_count_take_at_index],
--       rw [adv.to_query_count_of_mem_support_seed_and_run _ _ _ hrr],
--       rw [coe_query_count_of_mem_support_generate_seed hss],
--       refine indexed_list.take_at_index_le _ _ _,
--     end
--   ... = ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
--           rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) fp),
--           return (rr₁.fork_point, rr₂.fork_point)}⁆ :
--     begin
--       by_dist_equiv,
--       have := adv.generate_seed_bind_seed_and_run_dist_equiv y (adv.shared_query_count fp)
--         (indexed_list.take_at_index_le _ _ _),
--       rw_dist_equiv [this.symm, bind_bind_dist_equiv_assoc]
--     end

/--  -/
lemma le_prob_event_same_fork_point (adv : fork_adversary spec α β i) :
  ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / adv.q.succ
    ≤ ⁅same_fork_point | (fork adv).run y⁆ :=
calc ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / adv.q.succ
  -- Rewrite the probability of not getting `none` as the sum of each `some` possibility.
  = (∑ fp, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆) ^ 2 / adv.q.succ :
    by rw [prob_event_ne_none_eq_sum]
  -- Apply Jensen's inequality and cancel out the factor of `q.succ`.
  ... ≤ ∑ fp, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2 :
    le_trans (le_of_eq (by rw [one_add_one_eq_two, pow_one, ← card, card_fin]))
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
  ... ≤ ⁅same_fork_point | (fork adv).run y⁆ :
    begin
      rw [prob_event_same_fork_point],
      refine le_of_eq (finset.sum_congr rfl (λ fp _, _)),
      rw_dist_equiv [map_bind_dist_equiv _ _ fork_result.fork_points],
      pairwise_dist_equiv_deep,
    end


lemma prob_event_fork_success (adv : fork_adversary spec α β i) :
  ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ *
      (⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ / adv.q - (card (spec.range i))⁻¹)
    ≤ ⁅λ z, fork_success z = tt | (fork adv).run y⁆ :=
begin
  sorry
end

theorem le_fork_advantage (inp_gen : oracle_comp spec α) :
  let cf_advantage := (choose_fork_exp adv inp_gen).advantage in
  let fr_advantage := (fork_success_exp adv inp_gen).advantage in
  cf_advantage * (cf_advantage / adv.q - (card (spec.range i))⁻¹)
    ≤ fr_advantage :=
sorry

end prob_event_fork_success

end oracle_comp