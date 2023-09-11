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

variables {α β γ : Type} {spec : oracle_spec} {i : spec.ι} {q : ℕ}

structure fork_adversary (α β : Type) (i : spec.ι) (q : ℕ)
  extends sec_adversary spec α β :=
(choose_fork : α → β → option (fin q.succ))
(q_eq_bound : qb.get_count (sum.inr i) = q.succ)

def fork_adversary.success (adv : fork_adversary α β i q) (y : α) : β → Prop :=
λ x, adv.choose_fork y x ≠ none

noncomputable def fork_adversary.advantage (adv : fork_adversary α β i q) (y : α) : ℝ≥0∞ :=
⁅adv.success y | adv.run y⁆

section run_result

/-- Type to store the result of running the forking adversary a single time. -/
structure run_result (adv : fork_adversary α β i q) :=
(forking_point : option (fin q.succ))
(side_output : β)
(seed : (uniform_selecting ++ spec).query_seed)

/-- The index of the point in the seed chosen to fork on. -/
def run_result.get_fp {adv : fork_adversary α β i q} (rr : run_result adv) : fin q.succ :=
rr.forking_point.get_or_else 0

/-- The result of the query corresponding to the point being forked on. -/
def run_result.chosen_fork {adv : fork_adversary α β i q}
  (rr : run_result adv) : option (spec.range i) :=
(rr.seed (sum.inr i)).nth rr.get_fp

/-- The part of the seed designated to be reused by the result. -/
def run_result.shared_seed {adv : fork_adversary α β i q}
  (rr : run_result adv) : (uniform_selecting ++ spec).query_seed :=
rr.seed.take_at_index (sum.inr i) rr.get_fp

end run_result

section fork_result

def fork_result (adv : fork_adversary α β i q) :=
run_result adv × run_result adv

-- structure fork_result (adv : fork_adversary α β i q) :=
-- (chosen_fork₁ chosen_fork₂ : option (fin q.succ))
-- (side_output₁ side_output₂ : β)
-- (seed₁ seed₂ : query_seed (uniform_selecting ++ spec))

-- variable {adv : fork_adversary α β i q}

-- /-- Get the chosen fork point (the first one), defaulting to `0` if it doesn't exist. -/
-- @[inline, reducible] def fork_result.get_cf (x : fork_result adv) :
--   fin (q.succ) := x.chosen_fork₁.get_or_else 0

def fork_success (fr : fork_result adv) : Prop :=
x.chosen_fork₁ ≠ none ∧ x.chosen_fork₁ = x.chosen_fork₂ ∧
  (indexed_list.value_differs x.seed₁ x.seed₂ (sum.inr i) x.get_cf)

end fork_result

namespace fork_adversary

section seed_and_run

noncomputable def seed_and_run (adversary : fork_adversary α β i q) (y : α)
  (initial_seed : (uniform_selecting ++ spec).query_seed) :
  oracle_comp (uniform_selecting ++ spec) (run_result adversary) :=
do {
  fresh_seed ← generate_seed (adversary.qb - initial_seed),
  z ← simulate' seededₛₒ (adversary.run y) (initial_seed + fresh_seed),
  return (run_result.mk (adversary.choose_fork y z) z (initial_seed + fresh_seed))
}

/-- Fork a `fork_adversary` at the point defined by `cf`. -/
noncomputable def fork' (adversary : fork_adversary α β i q) (y : α) :
  oracle_comp (uniform_selecting ++ spec) (fork_result' adversary) :=
do {
  rr₁ ← adversary.seed_and_run y ∅,
  rr₂ ← adversary.seed_and_run y rr₁.shared_seed,
  return (rr₁, rr₂)
}

end seed_and_run

section of_choose_input

def of_choose_input (adv : sec_adversary spec β α)
  (i : spec.ι) (choose_input : α → β → spec.domain i) :
  fork_adversary β (α × query_log (uniform_selecting ++ spec)) i (adv.qb.get_count (sum.inr i)) :=
{ run := λ y, simulate loggingₛₒ (adv.run y) ∅,
  choose_fork := λ y z, begin
    have inp := choose_input z.1 y,
    have ts : list (spec.domain i) := (z.2 (sum.inr i)).map prod.fst,
    exact if inp ∈ ts then some ↑(list.index_of inp ts) else none,
  end,
  qb := adv.qb.increment (sum.inr i) 1,
  q_eq_bound := by simp,
  qb_is_bound := sorry
}

end of_choose_input

@[inline, reducible] def fresh_query_count (adversary : fork_adversary α β i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
query_count.of_nat (sum.inr i) (q.succ - fp)

@[inline, reducible] def shared_query_count (adversary : fork_adversary α β i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
adversary.qb.take_at_index (sum.inr i) fp

end fork_adversary

namespace oracle_comp

-- (seed i').nth (fp₁ + 1) ≠ (fresh_seed i').nth 0

/-- Fork a `fork_adversary` at the point defined by `cf`. -/
noncomputable def fork (adversary : fork_adversary α β i q) (y : α) :
  oracle_comp (uniform_selecting ++ spec) (fork_result adversary) :=
let i' : (uniform_selecting ++ spec).ι := sum.inr i in
do {
  -- Generate an initial seed with enouch values to reach the adversary's query bound.
  seed₁ ← generate_seed adversary.qb,
  -- Run the adversary using the seeded values and get the forking point
  z₁ ← simulate' seededₛₒ (adversary.run y) seed₁,
  fp₁ ← return ((adversary.choose_fork y z₁).get_or_else 0),
  -- Regenerate seed values after the chosen forking point.
  fresh_seed ← generate_seed (adversary.fresh_query_count fp₁),
  seed₂ ← return (seed₁.take_at_index i' fp₁ + fresh_seed),
  -- Run the adversary again using the new seeded values and get the forking point.
  z₂ ← simulate' seededₛₒ (adversary.run y) seed₂,
  fp₂ ← return ((adversary.choose_fork y z₂).get_or_else 0),
  return (fork_result.mk fp₁ fp₂ z₁ z₂ seed₁ seed₂)
}

noncomputable def fork_raw (adversary : fork_adversary α β i q) (y : α) :
  oracle_comp (uniform_selecting ++ spec) (fork_result adversary) :=
let i' : (uniform_selecting ++ spec).ι := sum.inr i in
do {
  -- Generate an initial seed with enouch values to reach the adversary's query bound.
  seed₁ ← generate_seed adversary.qb,
  -- Run the adversary using the seeded values and get the forking point
  z₁ ← simulate' seededₛₒ (adversary.run y) seed₁,
  fp₁ ← return ((adversary.choose_fork y z₁).get_or_else 0),
  -- Regenerate seed values after the chosen forking point.
  fresh_seed ← generate_seed (adversary.fresh_query_count fp₁),
  seed₂ ← return (seed₁.take_at_index i' fp₁ + fresh_seed),
  -- Run the adversary again using the new seeded values and get the forking point.
  z₂ ← simulate' seededₛₒ (adversary.run y) seed₂,
  fp₂ ← return ((adversary.choose_fork y z₂).get_or_else 0),
  return (fork_result.mk fp₁ fp₂ z₁ z₂ seed₁ seed₂)
}

-- noncomputable def fork (adversary : fork_adversary α β i q) (y : α) :
--   oracle_comp (uniform_selecting ++ spec) (fork_result adversary) :=
-- let i' : (uniform_selecting ++ spec).ι := sum.inr i in
-- do {
--   -- Generate an initial seed with enouch values to reach the adversary's query bound.
--   seed ← generate_seed adversary.qb,
--   z₁ ← simulate' seededₛₒ (adversary.run y) seed,
--   fp₁ ← return ((adversary.choose_fork y z₁).get_or_else 0),
--   -- Regenerate seed values after the chosen forking point.
--   shared_seed ← return (seed.take_at_index i' fp₁),
--   fresh_seed ← generate_seed (adversary.fresh_query_count fp₁),
--   -- Run the adversary again using the new seeded values.
--   z₂ ← simulate' seededₛₒ (adversary.run y) (shared_seed + fresh_seed),
--   fp₂ ← return ((adversary.choose_fork y z₂).get_or_else 0),
--   -- Return the final result, assuming that both runs choose the same forking point
--   let success := (adversary.choose_fork y z₁).is_some ∧ fp₁ = fp₂ in
--   return (fork_result.mk (if success then fp₁ else none) fp₂ z₁ z₂ seed (shared_seed + fresh_seed))
-- }

variables (adv : fork_adversary α β i q) (y : α) (fr : fork_result adv)

-- lemma prob_output_nth_seed₁

/-- Both the resulting `query_seed`s from running `fork` have the same number of seeded values.
TODO: should this be a `to_query_count` function that matches `coe`? -/
lemma to_query_count_seed_eq_to_query_count_seed (h : fr ∈ (fork adv y).support) :
  (↑(fr.seed₁) : query_count (uniform_selecting ++ spec)) = ↑fr.seed₂ :=
begin
  sorry
end

/-- Up until the forking point, both resulting `query_seed`s have the same seed values. -/
lemma take_queries_seed_eq_take_queries_seed (h : fr ∈ (fork adv y).support) :
  (fr.seed₁.take_at_index (sum.inr i) fr.get_cf) =
    (fr.seed₂.take_at_index (sum.inr i) fr.get_cf) :=
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
  adv.choose_fork y fr.side_output₁ = fr.chosen_fork₁ ∧
    adv.choose_fork y fr.side_output₂ = fr.chosen_fork₂ :=
begin
  sorry
end

/-- If `fork` returns success then the adversary must have thrown away at least one value. -/
lemma choose_fork_ne_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  fr.chosen_fork₁ ≠ some q :=
begin
  sorry
end

/-- If `fork` returns success then the output after the forking point
TODO: this should have a small chance to fail instead. -/
lemma seed_differs_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  (fr.seed₁ (sum.inr i)).nth (fr.get_cf) ≠
    (fr.seed₂ (sum.inr i)).nth (fr.get_cf) :=
begin
  sorry
end

section prob_event_fork_success

/-- The set of all possible shared seeds for the two runs of the computation. -/
noncomputable def poss_shared_seeds (qc : query_count (uniform_selecting ++ spec))
  (i : spec.ι) (fp : fin q.succ) : finset (query_seed (uniform_selecting ++ spec)) :=
(generate_seed (qc.decrement (sum.inr i) fp)).fin_support

-- lemma prob_event_eq_of_fst_irrel (oa : oracle_comp spec α)
--   (p : β → γ → Prop) (f : α → β)
--   (hf : )

-- lemma prob_event_nth_ne (adv : fork_adversary α β i q) (cf : fin q.succ) :
--   ⁅λ fr, indexed_list.value_differs fr.seed₁ fr.seed₂ (sum.inr i) cf | fork adv y⁆ =
--     ⁅λ x, x.1 ≠ x.2 | $ᵗ (spec.range i) ×ₘ $ᵗ (spec.range i)⁆ :=
-- let i' : (uniform_selecting ++ spec).ι := sum.inr i in
-- calc ⁅λ fr, (fr.seed₁ (sum.inr i)).nth cf ≠ (fr.seed₂ (sum.inr i)).nth cf | fork adv y⁆ =
--   -- ⁅λ z, (z.1 i').nth cf ≠ (z.2 i').nth cf |
--   --     fork adv y >>= λ fr, return (fr.seed₁, fr.seed₂)⁆ :
--   --   begin
--   --     rw [← map_eq_bind_return_comp, prob_event_map']
--   --   end
--   ⁅λ z, z.1 ≠ z.2 | do {fr ← fork adv y, return ((fr.seed₁ i').nth cf, (fr.seed₂ i').nth cf)}⁆ :
--     begin
--       rw [← map_eq_bind_return_comp, prob_event_map'],
--     end
--   -- ⁅λ z, z.1 ≠ z.2 | do {}⁆
--   ... = ⁅λ x, x.1 ≠ x.2 | $ᵗ (spec.range i) ×ₘ $ᵗ (spec.range i)⁆ : begin

--   end

-- example : α × β × γ := (_, (_, _))

lemma prob_event_value_differs (adv : fork_adversary α β i q) :
  ⁅λ fr, indexed_list.value_differs fr.seed₁ fr.seed₂ (sum.inr i) fr.get_cf | fork adv y⁆ =
    1 - (fintype.card (spec.range i))⁻¹ :=
let i' : (uniform_selecting ++ spec).ι := sum.inr i in
calc ⁅λ fr, indexed_list.value_differs fr.seed₁ fr.seed₂ (sum.inr i) fr.get_cf | fork adv y⁆ =
  ⁅λ fr, (fr.seed₁ i').nth fr.get_cf ≠ (fr.seed₂ i').nth fr.get_cf | fork adv y⁆ :
    begin
      refl,
    end
  ... = ⁅λ z, (z.2.1 i').nth z.1 ≠ (z.2.2 i').nth z.1 |
      fork adv y >>= λ fr, return (fr.get_cf, (fr.seed₁, fr.seed₂))⁆ :
    begin
      sorry,
    end
  ... = ⁅λ z, (z.2.1 i').nth z.1 ≠ (z.2.2 i').nth z.1 |
      do {
        seed₁ ← ↑(generate_seed adv.qb),
        z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
        fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
        fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
        seed₂ ← return (seed₁.take_at_index i' fp₁ + fresh_seed),
        return (fp₁, (seed₁, seed₂))
      }⁆ :
    begin
      sorry,
    end
  ... = ⁅λ z, z.1 ≠ z.2 |
      do {
        seed₁ ← ↑(generate_seed adv.qb),
        z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
        fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
        fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
        seed₂ ← return (seed₁.take_at_index i' fp₁ + fresh_seed),
        return ((seed₁ i').nth fp₁, (seed₂ i').nth fp₁)
      }⁆ :
    begin
      sorry,
    end
  ... = ⁅λ z, z.1 ≠ z.2 |
      do {
        seed₁ ← ↑(generate_seed adv.qb),
        z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
        fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
        fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
        return ((seed₁ i').nth fp₁, (fresh_seed i').nth 0)
      }⁆ :
    begin
      sorry,
    end
  ... = ⁅λ z, z.1 ≠ z.2 |
      do {
        seed₁ ← ↑(generate_seed adv.qb),
        z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
        fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
        fresh_seed ← generate_seed (adv.fresh_query_count fp₁),
        return ((seed₁ i').nth fp₁, (fresh_seed i').nth 0)
      }⁆ :
    begin
      sorry,
    end
  ... = ⁅λ z, z.1 ≠ z.2 |
      do {
        seed₁ ← ↑(generate_seed adv.qb),
        z₁ ← simulate' seededₛₒ (adv.run y) seed₁,
        fp₁ ← return ((adv.choose_fork y z₁).get_or_else 0),
        return ((seed₁ i').nth fp₁)
      } ×ₘ (some <$> $ᵗ (spec.range i))⁆ :
    begin

    end
  ... = ⁅λ x, x.1 ≠ x.2 | $ᵗ (spec.range i) ×ₘ $ᵗ (spec.range i)⁆ :
    begin
      sorry,
    end
  ... = 1 - (fintype.card (spec.range i))⁻¹ :
    begin
      rw [prob_event_not],
      -- rw [prob_event_diagonal],
      simp_rw [prob_event_fst_eq_snd_eq_sum, prob_output_mprod,
        prob_output_uniform_select_fintype, finset.sum_const],
      simp only [fintype.card, ←mul_assoc, nsmul_eq_mul],
      rw [ennreal.mul_inv_cancel, one_mul],
      refine nat.cast_ne_zero.2 fintype.card_ne_zero,
      refine ennreal.nat_ne_top _,
      -- refine trans (prob_event_fst_eq_snd _) _,
    end

lemma prob_event_chosen_fork_ne_none_and_eq (adv : fork_adversary α β i q) :
  ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q ≤
    ⁅λ x, x.chosen_fork₁ ≠ none ∧ x.chosen_fork₁ = x.chosen_fork₂ | fork adv y⁆ :=
calc ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q
  = (∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$> adv.run y⁆) ^ 2 / q :
    sorry
  ... ≤ (∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$>
                          simulate' seededₛₒ (adv.run y) ∅⁆) ^ 2 / q :
    begin
      sorry
    end

  ... ≤ ∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$>
                          simulate' seededₛₒ (adv.run y) ∅⁆ ^ 2 :
    begin
      -- Apply jensens inequality to pull in the square
      sorry,
    end

  ... ≤  ∑ fp : fin q.succ, (∑ shared_seed in poss_shared_seeds adv.qb i fp,
      ⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) shared_seed⁆
        * (possible_outcomes (adv.qb.decrement (sum.inr i) fp))⁻¹) ^ 2 :
    begin
      -- Sum over all the possible seeds for that forking point, weighted by their number
      sorry
    end

  ... ≤ ∑ fp : fin q.succ, ∑ seed in poss_shared_seeds adv.qb i fp,
      (⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) seed⁆ ^ 2
        * (possible_outcomes (adv.qb.decrement (sum.inr i) fp))⁻¹) :
    begin
      -- Apply Jensens inequality to pull in the square, losing a "possible_outcomes" factor
      sorry
    end

  ... ≤ ∑ fp : fin q.succ, ∑ shared_seed in poss_shared_seeds adv.qb i fp,
      (⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) shared_seed⁆
        * (possible_outcomes (adv.shared_query_count fp))⁻¹)
         * ⁅= some fp | adv.choose_fork y <$> simulate' seededₛₒ (adv.run y) shared_seed⁆ :
    begin
      -- Pull out one of the probability factors
      sorry
    end
  ... = ⁅λ x, x.chosen_fork₁ ≠ none ∧ x.chosen_fork₁ = x.chosen_fork₂ | fork adv y⁆ :
    begin
      sorry
    end

theorem prob_event_ne_none_le_prob_event_fork_success (adv : fork_adversary α β i q) :
  ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q - (fintype.card (spec.range i))⁻¹ ≤
    ⁅fork_success | fork adv y⁆ :=
begin

end


end prob_event_fork_success

end oracle_comp