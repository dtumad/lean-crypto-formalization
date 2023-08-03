/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.seeded_oracle
import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.query_tracking.query_log.basic
import computational_monads.coercions.instances
import computational_monads.simulation_semantics.oracle_compose

/-!
# Forking Computations at a Query
-/

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec} {i : spec.ι} {q : ℕ}

namespace oracle_comp

section sec_adversary

structure sec_adversary (spec : oracle_spec) (α : Type) :=
(run : oracle_comp (uniform_selecting ++ spec) α)
(qb : oracle_comp.query_count (uniform_selecting ++ spec))

end sec_adversary

end oracle_comp


section forking_adversary

open oracle_comp

structure forking_adversary (α : Type) (i : spec.ι) (q : ℕ)
  extends sec_adversary spec α :=
(choose_fork : α → option (fin q.succ))
(q_eq_bound : qb (sum.inr i) = q)

def forking_adversary.success (adv : forking_adversary α i q) : α → Prop :=
λ x, adv.choose_fork x ≠ none

section fork_result

structure fork_result (adv : forking_adversary α i q) :=
(chosen_fork : option (fin q.succ))
(side_output₁ side_output₂ : α)
(seed₁ seed₂ : query_seed (uniform_selecting ++ spec))

variable {adv : forking_adversary α i q}

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

def of_choose_input (adv : sec_adversary spec α) (choose_input : α → spec.domain i) :
  forking_adversary (α × query_log (uniform_selecting ++ spec)) i (adv.qb (sum.inr i)) :=
{ run := simulate logging_oracle adv.run ∅,
  choose_fork := λ z, begin
    have inp := choose_input z.1,
    have ts : list (spec.domain i) := (z.2 (sum.inr i)).map prod.fst,
    exact if inp ∈ ts then some ↑(list.index_of inp ts) else none,
  end,
  qb := adv.qb,
  q_eq_bound := rfl
}

end of_choose_input

@[inline, reducible] def fresh_query_count (adversary : forking_adversary α i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
query_count.of_nat (sum.inr i) (q - fp)

@[inline, reducible] noncomputable def shared_query_count (adversary : forking_adversary α i q)
  (fp : fin q.succ) : query_count (uniform_selecting ++ spec) :=
adversary.qb - fresh_query_count adversary fp

end forking_adversary

end forking_adversary

namespace oracle_comp

/-- Fork a `forking_adversary` at the point defined by `cf`. -/
noncomputable def fork (adversary : forking_adversary α i q) :
  oracle_comp (uniform_selecting ++ spec) (fork_result adversary) :=
let i' : (uniform_selecting ++ spec).ι := sum.inr i in
do {
  -- Generate an initial seed with enouch values to reach the adversary's query bound.
  seed ← generate_seed adversary.qb,
  z₁ ← simulate' seeded_oracle adversary.run seed,
  fp₁ ← return ((adversary.choose_fork z₁).get_or_else 0),
  -- Regenerate seed values after the chosen forking point.
  shared_seed ← return (seed.take_queries i' fp₁),
  fresh_seed ← generate_seed (adversary.fresh_query_count fp₁),
  -- Run the adversary again using the new seeded values.
  z₂ ← simulate' seeded_oracle adversary.run (shared_seed ++ fresh_seed),
  fp₂ ← return ((adversary.choose_fork z₂).get_or_else 0),
  -- Return the final result, assuming that both runs choose the same forking point
  let success := (adversary.choose_fork z₁).is_some ∧ fp₁ = fp₂ ∧
                    (seed i').nth (fp₁ + 1) ≠ (fresh_seed i').nth 0 in
  return (fork_result.mk (if success then fp₁ else none) z₁ z₂ seed (shared_seed ++ fresh_seed))
}

variables (adversary : forking_adversary α i q) (fr : fork_result adversary)

/-- Both the resulting `query_seed`s from running `fork` have the same number of seeded values. -/
lemma to_query_count_seed_eq_to_query_count_seed (h : fr ∈ (fork adversary).support) :
  fr.seed₁.to_query_count = fr.seed₂.to_query_count :=
begin
  sorry
end

/-- Up until the forking point, both resulting `query_seed`s have the same seed values. -/
lemma take_queries_seed_eq_take_queries_seed (h : fr ∈ (fork adversary).support) :
  (fr.seed₁.take_queries (sum.inr i) fr.get_cf) =
    (fr.seed₁.take_queries (sum.inr i) fr.get_cf) :=
begin
  sorry
end

/-- The first side output is in the support of simulating the adversary with the first seed. -/
lemma mem_support_simulate'_seed₁ (h : fr ∈ (fork adversary).support) :
  fr.side_output₁ ∈ (simulate' seeded_oracle adversary.run fr.seed₁).support :=
begin
  sorry,
end

/-- The second side output is in the support of simulating the adversary with the second seed. -/
lemma mem_support_simulate'_seed₂ (h : fr ∈ (fork adversary).support) :
  fr.side_output₂ ∈ (simulate' seeded_oracle adversary.run fr.seed₂).support :=
begin
  sorry,
end

/-- If `fork` returns success then both runs chose the same fork value. -/
lemma choose_fork_eq_of_fork_success (h : fr ∈ (fork adversary).support) (hfr : fork_success fr) :
  adversary.choose_fork fr.side_output₁ = fr.chosen_fork ∧
    adversary.choose_fork fr.side_output₂ = fr.chosen_fork :=
begin
  sorry
end

/-- If `fork` returns success then the adversary must have thrown away at least one value. -/
lemma choose_fork_ne_of_fork_success (h : fr ∈ (fork adversary).support) (hfr : fork_success fr) :
  fr.chosen_fork ≠ some q :=
begin
  sorry
end

/-- If `fork` returns success then the output after the forking point-/
lemma seed_differs_of_fork_success (h : fr ∈ (fork adversary).support) (hfr : fork_success fr) :
  (fr.seed₁ (sum.inr i)).nth (fr.get_cf + 1) ≠
    (fr.seed₂ (sum.inr i)).nth (fr.get_cf + 1) :=
begin
  sorry
end

theorem prob_event_fork_success : ⁅fork_success | fork adversary⁆ ≥
  ⁅(≠) none | adversary.choose_fork <$> adversary.run⁆ ^ 2 / q - (fintype.card (spec.range i))⁻¹ :=
begin
  sorry
end

end oracle_comp