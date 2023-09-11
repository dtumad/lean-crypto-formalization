/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging_oracle
import computational_monads.simulation_semantics.constructions.seeded_oracle
import computational_monads.distribution_semantics.option
import crypto_foundations.sec_adversary

/-!
# Forking Computations at a Query
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} {i : spec.ι} {q : ℕ}

/-- A forking adversary is a `sec_adversary _ α β` along with functions to define forking behavior.
`i` is the index of the oracle whose queries will be forked after a first execution.
`q` is a bound on the number of oracles made by the adversary, higher gives worse security bounds.
The function `choose_fork` takes an input and output pair, and returns an index at which the
queries should be forked (see `of_choose_input` to do this from a chosen query input value). -/
structure fork_adversary (α β : Type) (i : spec.ι) (q : ℕ)
  extends sec_adversary (uniform_selecting ++ spec) α β :=
(choose_fork : α → β → option (fin q.succ))
(q_eq_bound : qb.get_count (sum.inr i) = q.succ)

noncomputable def fork_adversary.advantage (adv : fork_adversary α β i q) (y : α) : ℝ≥0∞ :=
⁅(≠) none | adv.choose_fork y <$> adv.run y⁆

/-- Type to store the result of running the forking adversary a single time. -/
structure run_result (adv : fork_adversary α β i q) :=
(fork_point : option (fin q.succ))
(side_output : β)
(seed : (uniform_selecting ++ spec).query_seed)

/-- Type to store the result of running the forking adversary both times. -/
def fork_result (adv : fork_adversary α β i q) :=
run_result adv × run_result adv

namespace run_result

variable {adv : fork_adversary α β i q}

def get_fp (rr : run_result adv) : fin q.succ := rr.fork_point.get_or_else 0
def chosen_fork (rr : run_result adv) : option (spec.range i) :=
(rr.seed (sum.inr i)).nth rr.get_fp
def shared_seed (rr : run_result adv) : (uniform_selecting ++ spec).query_seed :=
rr.seed.take_at_index (sum.inr i) rr.get_fp

end run_result

namespace fork_result

variable {adv : fork_adversary α β i q}

@[inline, reducible] def fork_point₁ (fr : fork_result adv) := fr.1.fork_point
@[inline, reducible] def fork_point₂ (fr : fork_result adv) := fr.2.fork_point
@[inline, reducible] def fork_points (fr : fork_result adv) := (fr.fork_point₁, fr.fork_point₂)
@[inline, reducible] def chosen_fork₁ (fr : fork_result adv) := fr.1.chosen_fork
@[inline, reducible] def chosen_fork₂ (fr : fork_result adv) := fr.2.chosen_fork
@[inline, reducible] def side_output₁ (fr : fork_result adv) := fr.1.side_output
@[inline, reducible] def side_output₂ (fr : fork_result adv) := fr.2.side_output
@[inline, reducible] def seed₁ (fr : fork_result adv) := fr.1.seed
@[inline, reducible] def seed₂ (fr : fork_result adv) := fr.2.seed

end fork_result

section success

variable {adv : fork_adversary α β i q}

@[derive decidable] def same_fork_point (fr : fork_result adv) : Prop :=
fr.fork_point₁ ≠ none ∧ fr.fork_point₁ = fr.fork_point₂

lemma prob_event_same_fork_point (ofr : oracle_comp spec' (fork_result adv)) :
  ⁅same_fork_point | ofr⁆ =
    ∑ fp : fin q.succ, ⁅= (some fp, some fp) | fork_result.fork_points <$> ofr⁆ :=
calc ⁅same_fork_point | ofr⁆ = ⁅λ z, z.1 ≠ none ∧ z.1 = z.2 | fork_result.fork_points <$> ofr⁆ :
    symm (prob_event_map' ofr fork_result.fork_points _)
  ... = ∑ fp : fin q.succ, ⁅= (some fp, some fp) | fork_result.fork_points <$> ofr⁆ :
    begin
      rw [prob_event_eq_tsum_ite, ennreal.tsum_prod', ennreal.tsum_option],
      refine trans _ (zero_add _),
      congr' 1,
      {
        refine ennreal.tsum_eq_zero.2 (λ z, _),
        simp only [set.mem_def, ne.def, eq_self_iff_true, not_true, false_and, if_false],
      },
      {
        refine trans _ (tsum_eq_sum _),
        {
          refine tsum_congr (λ fp, _),
          refine trans (tsum_eq_single (some fp) _) _,
          {
            simp only [set.mem_def, ne.def, not_false_iff, true_and, ite_eq_right_iff,
              prob_output_eq_zero_iff, support_map],
            intros fp' h1 h2,
            refine (h1 h2.symm).elim,
          },
          {
            simp only [set.mem_def, ne.def, not_false_iff, eq_self_iff_true, and_self, if_true],
          }
        },
        {
          simp only [finset.mem_univ, not_true, is_empty.forall_iff, forall_const],
        }
      }
    end

def fork_success (fr : fork_result adv) : Prop :=
match fr.fork_point₁ with
| none := false
| some fp := fr.fork_point₂ = some fp ∧
    indexed_list.value_differs fr.seed₁ fr.seed₂ (sum.inr i) fp
end

end success

namespace fork_adversary

@[inline, reducible] def fresh_query_count (adv : fork_adversary α β i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
query_count.of_nat (sum.inr i) (q.succ - fp)

@[inline, reducible] def shared_query_count (adv : fork_adversary α β i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
adv.qb.take_at_index (sum.inr i) fp

section seed_and_run

noncomputable def seed_and_run (adv : fork_adversary α β i q) (y : α)
  (initial_seed : (uniform_selecting ++ spec).query_seed) :
  oracle_comp (uniform_selecting ++ spec) (run_result adv) :=
do {
  fresh_seed ← generate_seed (adv.qb - initial_seed),
  z ← simulate' seededₛₒ (adv.run y) (initial_seed + fresh_seed),
  return (run_result.mk (adv.choose_fork y z) z (initial_seed + fresh_seed))
}

variables (adv : fork_adversary α β i q) (y : α)

lemma generate_seed_bind_seed_and_run_dist_equiv
  (qc : (uniform_selecting ++ spec).query_count) (hqc : qc ≤ adv.qb) :
  do {qs ← ↑(generate_seed qc), adv.seed_and_run y qs} ≃ₚ adv.seed_and_run y ∅ :=
begin
  simp [seed_and_run],
  rw_dist_equiv [generate_seed_bind_split_of_le _ _ hqc],
  pairwise_dist_equiv with qs hqs,
  rw [support_coe_sub_spec] at hqs,
  rw [← coe_query_count_of_mem_support_generate_seed hqs, indexed_list.coe_query_count_eq],
end

lemma prob_output_fork_point_map_seed_and_run (fp : fin q.succ) :
  ⁅= some fp | run_result.fork_point <$> adv.seed_and_run y ∅⁆ =
    ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ :=
begin
  rw_dist_equiv [map_bind_dist_equiv, map_bind_dist_equiv, map_return_dist_equiv],
  simp only [indexed_list.coe_query_count_eq, indexed_list.to_query_count_empty,
    query_count.sub_empty, indexed_list.empty_add],
  refine trans (bind_bind_dist_equiv_assoc _ _ _) _,
  rw [map_eq_bind_return_comp],
  rw_dist_equiv [seeded_oracle.generate_seed_bind_simulate'_dist_equiv]
end

lemma to_query_count_of_mem_support_seed_and_run (qs : (uniform_selecting ++ spec).query_seed)
  (rr : run_result adv) (hrr : rr ∈ (adv.seed_and_run y qs).support)
  (h : ↑qs ≤ adv.qb) : rr.seed.to_query_count = adv.qb :=
begin
  rw [seed_and_run] at hrr,
  simp only [mem_support_bind_iff, mem_support_return_iff] at hrr,
  obtain ⟨init_s, hinit, z, hz, hzrr⟩ := hrr,
  rw [support_coe_sub_spec] at hinit,
  have := coe_query_count_of_mem_support_generate_seed hinit,
  rw [indexed_list.coe_query_count_eq] at this,
  simp [hzrr, this],
  refine query_count.get_count_ext _ _ (λ i, _),
  simp,
  rw [← nat.add_sub_assoc, nat.add_sub_cancel_left],
  have := query_count.get_count_le_get_count h i,
  simpa [indexed_list.get_count_to_query_count] using this,
end

lemma shared_seed_of_mem_support_seed_and_run (qs : (uniform_selecting ++ spec).query_seed)
  (rr : run_result adv) (hrr : rr ∈ (adv.seed_and_run y qs).support) :
  rr.seed.take_to_count ↑qs = qs :=
begin
  rw [seed_and_run] at hrr,
  simp only [mem_support_bind_iff, mem_support_return_iff] at hrr,
  obtain ⟨init_s, hinit, z, hz, hzrr⟩ := hrr,
  simp only [hzrr, indexed_list.take_to_count_add_left],
end


end seed_and_run

end fork_adversary

namespace oracle_comp

/-- Fork a `fork_adversary` at the point defined by `cf`. -/
noncomputable def fork (adv : fork_adversary α β i q) (y : α) :
  oracle_comp (uniform_selecting ++ spec) (fork_result adv) :=
do {
  rr₁ ← adv.seed_and_run y ∅,
  rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) rr₁.get_fp),
  return (rr₁, rr₂)
}

variables (adv : fork_adversary α β i q) (y : α) (fr : fork_result adv)

-- lemma prob_output_nth_seed₁

/-- Both the resulting `query_seed`s from running `fork` have the same number of seeded values.
TODO: should this be a `to_query_count` function that matches `coe`? -/
lemma to_query_count_seed_eq_to_query_count_seed (h : fr ∈ (fork adv y).support) :
  fr.seed₁.to_query_count = fr.seed₂.to_query_count :=
begin
  sorry
end

/-- Up until the forking point, both resulting `query_seed`s have the same seed values. -/
lemma take_queries_seed_eq_take_queries_seed (h : fr ∈ (fork adv y).support) :
  (fr.seed₁.take_at_index (sum.inr i) fr.1.get_fp) =
    (fr.seed₂.take_at_index (sum.inr i) fr.1.get_fp) :=
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
  fr.fork_point₁ ≠ some q :=
begin
  sorry
end

/-- If `fork` returns success then the output after the forking point
TODO: this should have a small chance to fail instead. -/
lemma seed_differs_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  (fr.seed₁ (sum.inr i)).nth (fr.1.get_fp) ≠
    (fr.seed₂ (sum.inr i)).nth (fr.2.get_fp) :=
begin
  sorry
end

section prob_event_fork_success

/-- The set of all possible shared seeds for the two runs of the computation. -/
noncomputable def poss_shared_seeds (qc : query_count (uniform_selecting ++ spec))
  (i : spec.ι) (fp : fin q.succ) : finset (query_seed (uniform_selecting ++ spec)) :=
(generate_seed (qc.decrement (sum.inr i) fp)).fin_support

/-- -/
lemma le_prob_output_fork_points (adv : fork_adversary α β i q) (fp : fin q.succ) :
  ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2 ≤
    ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
      rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) fp),
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
          rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) fp),
          return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    begin
      pairwise_dist_equiv with shared_seed hss rr hrr,
      suffices : shared_seed = indexed_list.take_at_index rr.seed (sum.inr i) ↑fp,
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
          rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) fp),
          return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    begin
      by_dist_equiv,
      have := adv.generate_seed_bind_seed_and_run_dist_equiv y (adv.shared_query_count fp)
        (indexed_list.take_at_index_le _ _ _),
      rw_dist_equiv [this.symm, bind_bind_dist_equiv_assoc]
    end

/--  -/
lemma le_prob_event_same_fork_point (adv : fork_adversary α β i q) :
  adv.advantage y ^ 2 / q.succ ≤ ⁅same_fork_point | fork adv y⁆ :=
calc adv.advantage y ^ 2 / q.succ = ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q.succ : rfl
  -- Rewrite the probability of not getting `none` as the sum of each `some` possibility.
  ... = (∑ fp, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆) ^ 2 / q.succ :
    by rw [prob_event_ne_none_eq_sum]
  -- Apply Jensen's inequality and cancel out the factor of `q.succ`.
  ... ≤ ∑ fp, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ ^ 2 :
    le_trans (le_of_eq (by rw [one_add_one_eq_two, pow_one, ← fintype.card, fintype.card_fin]))
      (ennreal.pow_sum_div_card_le_sum_pow _ _ (λ _ _, prob_output_ne_top _ _) 1)
  -- Apply `le_prob_output_fork_points` to the inner probability calculation.
  ... ≤ ∑ fp, ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
            rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) ↑fp),
            return (rr₁.fork_point, rr₂.fork_point)}⁆ :
    finset.sum_le_sum (λ fp hfp, by apply le_prob_output_fork_points)
  ... = ∑ fp, ⁅= (some fp, some fp) | do {rr₁ ← adv.seed_and_run y ∅,
            rr₂ ← adv.seed_and_run y (rr₁.seed.take_at_index (sum.inr i) (rr₁.fork_point.get_or_else 0)),
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





theorem prob_event_fork_success (adv : fork_adversary α β i q) :
  adv.advantage y * (adv.advantage y / q - (fintype.card (spec.range i))⁻¹) ≤
    ⁅fork_success | fork adv y⁆ :=
begin
  sorry
end

-- lemma prob_event_value_differs (adv : fork_adversary α β i q) :
--   ⁅λ fr, indexed_list.value_differs fr.seed₁ fr.seed₂ (sum.inr i) fr.get_cf | fork adv y⁆ =
--     1 - (fintype.card (spec.range i))⁻¹ :=
-- let i' : (uniform_selecting ++ spec).ι := sum.inr i in
-- calc ⁅λ fr, indexed_list.value_differs fr.seed₁ fr.seed₂ (sum.inr i) fr.get_cf | fork adv y⁆ =
--   ... = ⁅λ x, x.1 ≠ x.2 | $ᵗ (spec.range i) ×ₘ $ᵗ (spec.range i)⁆ :
--     begin
--       sorry,
--     end
--   ... = 1 - (fintype.card (spec.range i))⁻¹ :
--     begin
--       rw [prob_event_not],
--       -- rw [prob_event_diagonal],
--       simp_rw [prob_event_fst_eq_snd_eq_sum, prob_output_mprod,
--         prob_output_uniform_select_fintype, finset.sum_const],
--       simp only [fintype.card, ←mul_assoc, nsmul_eq_mul],
--       rw [ennreal.mul_inv_cancel, one_mul],
--       refine nat.cast_ne_zero.2 fintype.card_ne_zero,
--       refine ennreal.nat_ne_top _,
--       -- refine trans (prob_event_fst_eq_snd _) _,
--     end

-- lemma prob_event_chosen_fork_ne_none_and_eq (adv : fork_adversary α β i q) :
--   ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q ≤
--     ⁅λ x, x.chosen_fork₁ ≠ none ∧ x.chosen_fork₁ = x.chosen_fork₂ | fork adv y⁆ :=
-- calc ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q
--   = (∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆) ^ 2 / q :
--     sorry
--   ... ≤ (∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$>
--                           simulate' seededₛₒ (adv.run y) ∅⁆) ^ 2 / q :
--     begin
--       sorry
--     end

--   ... ≤ ∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$>
--                           simulate' seededₛₒ (adv.run y) ∅⁆ ^ 2 :
--     begin
--       -- Apply jensens inequality to pull in the square
--       sorry,
--     end

--   ... ≤  ∑ fp : fin q.succ, (∑ shared_seed in poss_shared_seeds adv.qb i fp,
--       ⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) shared_seed⁆
--         * (possible_outcomes (adv.qb.decrement (sum.inr i) fp))⁻¹) ^ 2 :
--     begin
--       -- Sum over all the possible seeds for that forking point, weighted by their number
--       sorry
--     end

--   ... ≤ ∑ fp : fin q.succ, ∑ seed in poss_shared_seeds adv.qb i fp,
--       (⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) seed⁆ ^ 2
--         * (possible_outcomes (adv.qb.decrement (sum.inr i) fp))⁻¹) :
--     begin
--       -- Apply Jensens inequality to pull in the square, losing a "possible_outcomes" factor
--       sorry
--     end

--   ... ≤ ∑ fp : fin q.succ, ∑ shared_seed in poss_shared_seeds adv.qb i fp,
--       (⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) shared_seed⁆
--         * (possible_outcomes (adv.shared_query_count fp))⁻¹)
--          * ⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) shared_seed⁆ :
--     begin
--       -- Pull out one of the probability factors
--       sorry
--     end
--   ... = ⁅λ x, x.chosen_fork₁ ≠ none ∧ x.chosen_fork₁ = x.chosen_fork₂ | fork adv y⁆ :
--     begin
--       sorry
--     end

-- theorem prob_event_ne_none_le_prob_event_fork_success (adv : fork_adversary α β i q) :
--   ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q - (fintype.card (spec.range i))⁻¹ ≤
--     ⁅fork_success | fork adv y⁆ :=
-- begin

-- end


-- ⁅λ fr, (fr.seed₁ i').nth fr.get_cf ≠ (fr.seed₂ i').nth fr.get_cf | fork adv y⁆ :
--     begin
--       refl,
--     end
--   ... = ⁅λ z, (z.2.1 i').nth z.1 ≠ (z.2.2 i').nth z.1 |
--       fork adv y >>= λ fr, return (fr.get_cf, (fr.seed₁, fr.seed₂))⁆ :
--     begin
--       sorry,
--     end
--   ... = ⁅λ z, (z.2.1 i').nth z.1 ≠ (z.2.2 i').nth z.1 |
--       do {
--         seed₁ ← ↑(generate_seed adv.qb),
--         z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
--         fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
--         fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
--         seed₂ ← return (seed₁.take_at_index i' fp₁ + fresh_seed),
--         return (fp₁, (seed₁, seed₂))
--       }⁆ :
--     begin
--       sorry,
--     end
--   ... = ⁅λ z, z.1 ≠ z.2 |
--       do {
--         seed₁ ← ↑(generate_seed adv.qb),
--         z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
--         fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
--         fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
--         seed₂ ← return (seed₁.take_at_index i' fp₁ + fresh_seed),
--         return ((seed₁ i').nth fp₁, (seed₂ i').nth fp₁)
--       }⁆ :
--     begin
--       sorry,
--     end
--   ... = ⁅λ z, z.1 ≠ z.2 |
--       do {
--         seed₁ ← ↑(generate_seed adv.qb),
--         z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
--         fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
--         fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
--         return ((seed₁ i').nth fp₁, (fresh_seed i').nth 0)
--       }⁆ :
--     begin
--       sorry,
--     end
--   ... = ⁅λ z, z.1 ≠ z.2 |
--       do {
--         seed₁ ← ↑(generate_seed adv.qb),
--         z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
--         fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
--         fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
--         return ((seed₁ i').nth fp₁, (fresh_seed i').nth 0)
--       }⁆ :
--     begin
--       sorry,
--     end
--   ... = ⁅λ z, z.1 ≠ z.2 |
--       do {
--         seed₁ ← ↑(generate_seed adv.qb),
--         z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
--         fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
--         return ((seed₁ i').nth fp₁)
--       } ×ₘ (some <$> $ᵗ (spec.range i))⁆ :
--     begin

--     end


end prob_event_fork_success

end oracle_comp


-- TODO: for the hhs sig
section of_choose_input

def of_choose_input (adv : sec_adversary (uniform_selecting ++ spec) β α)
  (i : spec.ι) (choose_input : α → β → spec.domain i) :
  fork_adversary β (α × query_log (uniform_selecting ++ spec)) i (adv.qb.get_count (sum.inr i)) :=
{ run := λ y, simulate loggingₛₒ (adv.run y) ∅,
  choose_fork := λ y z, let inp := choose_input z.1 y in
    let ts : list (spec.domain i) := (z.2 (sum.inr i)).map prod.fst in
    if inp ∈ ts then some ↑(list.index_of inp ts) else none,
  qb := adv.qb.increment (sum.inr i) 1,
  q_eq_bound := by simp only [query_count.get_count_increment, eq_self_iff_true, if_true],
  qb_is_bound := λ y, logging_oracle.queries_at_most_simulate _ _
    (queries_at_most_trans _ _ _ (adv.qb_is_bound y) (indexed_list.le_add_values _ _)) _ }

end of_choose_input