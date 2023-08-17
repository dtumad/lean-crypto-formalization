/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.query_tracking.query_log.basic
import computational_monads.coercions.instances
import computational_monads.simulation_semantics.oracle_compose
import crypto_foundations.sec_adversary

/-!
# Forking Computations at a Query
-/

open_locale big_operators ennreal
open oracle_comp oracle_spec

variables {α β γ : Type} {spec : oracle_spec} {i : spec.ι} {q : ℕ}

section forking_adversary

structure forking_adversary (α β : Type) (i : spec.ι) (q : ℕ)
  extends sec_adversary spec α β :=
(choose_fork : α → β → option (fin q.succ))
(q_eq_bound : qb.get_count (sum.inr i) = q)

def forking_adversary.success (adv : forking_adversary α β i q) (y : α) : β → Prop :=
λ x, adv.choose_fork y x ≠ none

noncomputable def forking_adversary.advantage (adv : forking_adversary α β i q) (y : α) : ℝ≥0∞ :=
⁅adv.success y | adv.run y⁆

section fork_result

structure fork_result (adv : forking_adversary α β i q) :=
(chosen_fork : option (fin q.succ))
(side_output₁ side_output₂ : β)
(seed₁ seed₂ : query_seed (uniform_selecting ++ spec))

variable {adv : forking_adversary α β i q}

@[inline, reducible] def fork_result.get_cf (x : fork_result adv) :
  fin (q.succ) := x.chosen_fork.get_or_else 0

def fork_success (x : fork_result adv) : Prop :=
match x.chosen_fork with
| none := false
| (some cf) := query_seed.seed_differs x.seed₁ x.seed₂ (sum.inr i) cf
end

end fork_result

namespace forking_adversary

section of_choose_input

def of_choose_input (adv : sec_adversary spec β α)
  (i : spec.ι) (choose_input : α → β → spec.domain i) :
  forking_adversary β (α × query_log (uniform_selecting ++ spec)) i (adv.qb.get_count (sum.inr i)) :=
{ run := λ y, simulate logging_oracle (adv.run y) ∅,
  choose_fork := λ y z, begin
    have inp := choose_input z.1 y,
    have ts : list (spec.domain i) := (z.2 (sum.inr i)).map prod.fst,
    exact if inp ∈ ts then some ↑(list.index_of inp ts) else none,
  end,
  qb := adv.qb,
  q_eq_bound := rfl
}

end of_choose_input

@[inline, reducible] def fresh_query_count (adversary : forking_adversary α β i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
query_count.of_nat (sum.inr i) (q - fp)

@[inline, reducible] noncomputable def shared_query_count (adversary : forking_adversary α β i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
adversary.qb - fresh_query_count adversary fp

end forking_adversary

end forking_adversary

namespace oracle_comp

-- (seed i').nth (fp₁ + 1) ≠ (fresh_seed i').nth 0

/-- Fork a `forking_adversary` at the point defined by `cf`. -/
noncomputable def fork (adversary : forking_adversary α β i q) (y : α) :
  oracle_comp (uniform_selecting ++ spec) (fork_result adversary) :=
let i' : (uniform_selecting ++ spec).ι := sum.inr i in
do {
  -- Generate an initial seed with enouch values to reach the adversary's query bound.
  seed ← generate_seed adversary.qb,
  z₁ ← simulate' seeded_oracle (adversary.run y) seed,
  fp₁ ← return ((adversary.choose_fork y z₁).get_or_else 0),
  -- Regenerate seed values after the chosen forking point.
  shared_seed ← return (seed.take_at_index i' fp₁),
  fresh_seed ← generate_seed (adversary.fresh_query_count fp₁),
  -- Run the adversary again using the new seeded values.
  z₂ ← simulate' seeded_oracle (adversary.run y) (shared_seed + fresh_seed),
  fp₂ ← return ((adversary.choose_fork y z₂).get_or_else 0),
  -- Return the final result, assuming that both runs choose the same forking point
  let success := (adversary.choose_fork y z₁).is_some ∧ fp₁ = fp₂ in
  return (fork_result.mk (if success then fp₁ else none) z₁ z₂ seed (shared_seed + fresh_seed))
}

variables (adv : forking_adversary α β i q) (y : α) (fr : fork_result adv)

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
  fr.side_output₁ ∈ (simulate' seeded_oracle (adv.run y) fr.seed₁).support :=
begin
  sorry,
end

/-- The second side output is in the support of simulating the adversary with the second seed. -/
lemma mem_support_simulate'_seed₂ (h : fr ∈ (fork adv y).support) :
  fr.side_output₂ ∈ (simulate' seeded_oracle (adv.run y) fr.seed₂).support :=
begin
  sorry,
end

/-- If `fork` returns success then both runs chose the same fork value. -/
lemma choose_fork_eq_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  adv.choose_fork y fr.side_output₁ = fr.chosen_fork ∧
    adv.choose_fork y fr.side_output₂ = fr.chosen_fork :=
begin
  sorry
end

/-- If `fork` returns success then the adversary must have thrown away at least one value. -/
lemma choose_fork_ne_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  fr.chosen_fork ≠ some q :=
begin
  sorry
end

/-- If `fork` returns success then the output after the forking point
TODO: this should have a small chance to fail instead. -/
lemma seed_differs_of_fork_success (h : fr ∈ (fork adv y).support) (hfr : fork_success fr) :
  (fr.seed₁ (sum.inr i)).nth (fr.get_cf + 1) ≠
    (fr.seed₂ (sum.inr i)).nth (fr.get_cf + 1) :=
begin
  sorry
end

section prob_event_fork_success

/-- The set of all possible shared seeds for the two runs of the computation. -/
noncomputable def poss_shared_seeds (qc : query_count (uniform_selecting ++ spec))
  (i : spec.ι) (fp : fin q.succ) : finset (query_seed (uniform_selecting ++ spec)) :=
(generate_seed (qc.decrement (sum.inr i) fp)).fin_support

theorem prob_event_ne_none_le_prob_event_fork_success (adv : forking_adversary α β i q) :
  ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q ≤
    ⁅fork_success | fork adv y⁆ :=
calc ⁅(≠) none | adv.choose_fork y <$> adv.run y⁆ ^ 2 / q

  ≤ (∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$>
                          simulate' seeded_oracle (adv.run y) ∅⁆) ^ 2 / q :
    begin
      sorry
    end

  ... ≤ ∑ fp : fin q.succ, ⁅= some fp | adv.choose_fork y <$>
                          simulate' seeded_oracle (adv.run y) ∅⁆ ^ 2 :
    begin
      -- Apply jensens inequality to pull in the square
      sorry,
    end

  ... ≤  ∑ fp : fin q.succ, (∑ seed in poss_shared_seeds adv.qb i fp,
      ⁅= some fp | adv.choose_fork y <$> simulate' seeded_oracle (adv.run y) seed⁆
        * (possible_outcomes (adv.qb.decrement (sum.inr i) fp))⁻¹) ^ 2 :
    begin
      -- Sum over all the possible seeds for that forking point, weighted by their number
      sorry
    end

  ... ≤ ∑ fp : fin q.succ, ∑ seed in poss_shared_seeds adv.qb i fp,
      (⁅= some fp | adv.choose_fork y <$> simulate' seeded_oracle (adv.run y) seed⁆ ^ 2
        * (possible_outcomes (adv.qb.decrement (sum.inr i) fp))⁻¹) :
    begin
      -- Apply Jensens inequality to pull in the square, losing a "possible_outcomes" factor
      sorry
    end

  ... ≤ ∑ fp : fin q.succ, ∑ seed in poss_shared_seeds adv.qb i fp,
      (⁅= some fp | adv.choose_fork y <$> simulate' seeded_oracle (adv.run y) seed⁆
        * (possible_outcomes (adv.qb.decrement (sum.inr i) fp))⁻¹)
         * ⁅= some fp | adv.choose_fork y <$> simulate' seeded_oracle (adv.run y) seed⁆ :
    begin
      -- Pull out one of the probability factors
      sorry
    end

  ... = ⁅fork_success | fork adv y⁆ :
    begin
      -- Essentially by definition on paper but will require mucking around with the counts
      sorry
    end


end prob_event_fork_success

end oracle_comp