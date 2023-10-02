/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging_oracle
import computational_monads.simulation_semantics.constructions.seeded_oracle
import computational_monads.simulation_semantics.constructions.uniform_oracle
import computational_monads.distribution_semantics.option
import crypto_foundations.sec_adversary

/-!
# Forkable Computations

This file defines an "adversary" `fork_adversary` for a computation that `fork` can be run on.
The name adversary is based on the fact that forking is usually done in a security game reduction.
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' adv_spec exp_spec : oracle_spec} {i : spec.ι} --{q : ℕ}

/-- A forking adversary is a `sec_adversary _ α β` along with functions to define forking behavior.
`i` is the index of the oracle whose queries will be forked after a first execution.
`q` is a bound on the number of oracles made by the adversary, higher gives worse security bounds.
The function `choose_fork` takes an input and output pair, and returns an index at which the
queries should be forked (see `of_choose_input` to do this from a chosen query input value). -/
structure fork_adversary (spec : oracle_spec) (α β : Type)
  (i : spec.ι) extends sec_adversary spec α β :=
(choose_fork : α → β → option (fin (qb.get_count i).succ))

@[inline, reducible] def fork_adversary.q (adv : fork_adversary spec α β i) := adv.qb.get_count i

-- noncomputable def fork_adversary.cf_experiment (adv : fork_adversary spec α β i) (inp_gen : oracle_comp spec α) :
--   base_sec_experiment spec α β :=
-- base_sec_experiment_of_is_valid inp_gen (λ x y, return (adv.choose_fork x y ≠ none)) uniformₛₒ

noncomputable def fork_adversary.cf_experiment
  (inp_gen : oracle_comp spec α)
  (adv : fork_adversary spec α β i) :
  sec_experiment spec spec α β unit unit unit :=
public_experiment inp_gen (λ _, idₛₒ)
  (λ x y, return (adv.choose_fork x y ≠ none)) uniformₛₒ

noncomputable def fork_adversary.cf_advantage (adv : fork_adversary spec α β i)
  (inp_gen : oracle_comp spec α) : ℝ≥0∞ :=
adv.advantage (adv.cf_experiment inp_gen)

-- noncomputable def fork_adversary.cf_advantage (adv : fork_adversary spec α β i) (y : α) :=
-- ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆

-- @[simps]
-- def choose_fork_experiment (adv : fork_adversary spec α β i q) (x : α) :
--   sec_experiment spec α β unit unit :=
-- { inp_gen := return (x, ()),
--   is_valid := λ x y, return (adv.choose_fork x.1 y.1 ≠ none) }

-- -- lemma choose_fork_experiment.inp_gen_eq

-- noncomputable def fork_adversary.cf_advantage (adv : fork_adversary spec α β i q) (x : α) : ℝ≥0∞ :=
-- adv.base_advantage (choose_fork_experiment adv x)

-- lemma cf_advantage_eq_prob_output_ne_none (adv : fork_adversary spec α β i q) (x : α) :
--   adv.cf_advantage x = ⁅(≠) none | adv.choose_fork x <$> adv.simulate_run (x, ())⁆ :=
-- begin
--   rw [fork_adversary.cf_advantage],
--   rw [base_advantage_eq_prob_output],
--   rw [choose_fork_experiment_inp_gen],
--   rw [prob_output_return_bind],

-- end

/-- Type to store the result of running the forking adversary a single time. -/
structure run_result (adv : fork_adversary spec α β i) :=
(fork_point : option (fin adv.q.succ))
(side_output : β)
(seed : spec.query_seed)

namespace run_result

variable {adv : fork_adversary spec α β i}

def get_fp (rr : run_result adv) : fin adv.q.succ := rr.fork_point.get_or_else 0
def chosen_fork (rr : run_result adv) : option (spec.range i) :=
(rr.seed i).nth rr.get_fp
def shared_seed (rr : run_result adv) : spec.query_seed :=
rr.seed.take_at_index i rr.get_fp

end run_result

/-- Type to store the result of running the forking adversary both times. -/
def fork_result (adv : fork_adversary spec α β i) :=
run_result adv × run_result adv

namespace fork_result

variables {adv : fork_adversary spec α β i} (fr : fork_result adv)

@[simp, inline, reducible] def fork_point₁ := fr.1.fork_point
@[simp, inline, reducible] def fork_point₂ := fr.2.fork_point
@[simp, inline, reducible] def fork_points := (fr.fork_point₁, fr.fork_point₂)
@[simp, inline, reducible] def chosen_fork₁ := fr.1.chosen_fork
@[simp, inline, reducible] def chosen_fork₂ := fr.2.chosen_fork
@[simp, inline, reducible] def side_output₁ := fr.1.side_output
@[simp, inline, reducible] def side_output₂ := fr.2.side_output
@[simp, inline, reducible] def seed₁ := fr.1.seed
@[simp, inline, reducible] def seed₂ := fr.2.seed

end fork_result

section success

variable {adv : fork_adversary spec α β i}

@[derive decidable] def same_fork_point (fr : fork_result adv) : Prop :=
fr.fork_point₁ ≠ none ∧ fr.fork_point₁ = fr.fork_point₂

lemma prob_event_same_fork_point (ofr : oracle_comp spec' (fork_result adv)) :
  ⁅same_fork_point | ofr⁆ =
    ∑ fp : fin adv.q.succ, ⁅= (some fp, some fp) | fork_result.fork_points <$> ofr⁆ :=
calc ⁅same_fork_point | ofr⁆ = ⁅λ z, z.1 ≠ none ∧ z.1 = z.2 | fork_result.fork_points <$> ofr⁆ :
    symm (prob_event_map' ofr fork_result.fork_points _)
  ... = ∑ fp : fin adv.q.succ, ⁅= (some fp, some fp) | fork_result.fork_points <$> ofr⁆ :
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

/-- Forking succeeds if both chosen forking points are the same,
and the seed at that index differs with the other -/
def fork_success (fr : fork_result adv) : bool :=
match fr.fork_point₁ with
| none := false
| some fp := fr.fork_point₂ = some fp ∧ fr.seed₁.value_differs fr.seed₂ i fp
end

lemma fork_success_iff_exists (fr : fork_result adv) : fork_success fr ↔
  ∃ fp : fin adv.q.succ, fr.fork_point₁ = some fp ∧ fr.fork_point₂ = some fp
    ∧ fr.seed₁.value_differs fr.seed₂ i fp :=
begin
  rcases fr with ⟨⟨fp₁, z₁, seed₁⟩, ⟨fp₂, z₂, seed₂⟩⟩,
  cases fp₁; simp [fork_success]
end

end success

namespace fork_adversary

@[inline, reducible] def fresh_query_count (adv : fork_adversary spec α β i)
  (fp : fin adv.q.succ) : query_count spec :=
query_count.of_nat i (adv.q.succ - fp)

@[inline, reducible] def shared_query_count (adv : fork_adversary spec α β i)
  (fp : fin adv.q.succ) : query_count spec :=
adv.qb.take_at_index i fp

section seed_and_run

variable [is_sub_spec uniform_selecting spec]

noncomputable def seed_and_run (adv : fork_adversary spec α β i)
  (y : α) (init_seed : spec.query_seed) :
  oracle_comp spec (run_result adv) :=
do {fresh_seed ← generate_seed (adv.qb - init_seed),
  z ← simulate' seededₛₒ (adv.run y) (init_seed + fresh_seed),
  return (run_result.mk (adv.choose_fork y z) z (init_seed + fresh_seed))}

variables (adv : fork_adversary spec α β i) (y : α)

lemma generate_seed_bind_seed_and_run_dist_equiv
  (qc : spec.query_count) (hqc : qc ≤ adv.qb) :
  do {qs ← ↑(generate_seed qc), adv.seed_and_run y qs} ≃ₚ adv.seed_and_run y ∅ :=
begin
  simp [seed_and_run],
  rw_dist_equiv [generate_seed_bind_split_of_le _ _ hqc],
  pairwise_dist_equiv with qs hqs,
  rw [support_coe_sub_spec] at hqs,
  rw [← coe_query_count_of_mem_support_generate_seed hqs, indexed_list.coe_query_count_eq],
end

lemma prob_output_fork_point_map_seed_and_run (fp : fin adv.q.succ) :
  ⁅= some fp | run_result.fork_point <$> adv.seed_and_run y ∅⁆ =
    ⁅= some fp | adv.choose_fork y <$> adv.run y⁆ :=
begin
  rw_dist_equiv [map_bind_dist_equiv, map_bind_dist_equiv, map_return_dist_equiv],
  simp only [indexed_list.coe_query_count_eq, indexed_list.to_query_count_empty,
    query_count.sub_empty, indexed_list.empty_add],
  refine trans (bind_bind_dist_equiv_assoc _ _ _) _,
  rw [oracle_comp.map_eq_bind_return_comp],
  rw_dist_equiv [seeded_oracle.generate_seed_bind_simulate'_dist_equiv]
end

lemma to_query_count_of_mem_support_seed_and_run (qs : spec.query_seed)
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

lemma take_to_count_seed_eq_seed (qs : spec.query_seed)
  (rr : run_result adv) (hrr : rr ∈ (adv.seed_and_run y qs).support) :
  rr.seed.take_to_count ↑qs = qs :=
begin
  rw [seed_and_run] at hrr,
  simp only [mem_support_bind_iff, mem_support_return_iff] at hrr,
  obtain ⟨init_s, hinit, z, hz, hzrr⟩ := hrr,
  simp only [hzrr, indexed_list.take_to_count_add_left],
end

lemma fork_point_eq_choose_fork (qs : spec.query_seed)
  (rr : run_result adv) (hrr : rr ∈ (adv.seed_and_run y qs).support) :
  rr.fork_point = adv.choose_fork y rr.side_output :=
begin
  rw [seed_and_run] at hrr, -- TODO: support lemma
  simp only [mem_support_bind_iff, mem_support_return_iff] at hrr,
  obtain ⟨init_s, hinit, z, hz, hzrr⟩ := hrr,
  rw [hzrr],
end

end seed_and_run

end fork_adversary