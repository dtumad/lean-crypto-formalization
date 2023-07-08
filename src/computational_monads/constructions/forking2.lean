/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.caching_oracle2
import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.seeded_oracle
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.oracle_compose
import computational_monads.simulation_semantics.constructions.uniform_oracle
import computational_monads.simulation_semantics.mask_state

open oracle_spec oracle_comp
open_locale big_operators ennreal

variables {α β γ T U : Type} {spec spec' : oracle_spec}
  [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U] [inhabited T]

section to_move

/-- Oracle that responds uniformly at random to any new queries,
but returns the same result to subsequent oracle queries.
Masking is used to hide the irrelevent state of the `uniform_oracle` -/
noncomputable def random_oracle {spec : oracle_spec} :
  sim_oracle spec uniform_selecting (query_cache spec) :=
((uniform_oracle spec) ∘ₛ cachingₛₒ).mask_state (equiv.prod_punit (query_cache spec))


instance query_log.has_emptyc : has_emptyc (query_log spec) := ⟨query_log.init _⟩

end to_move




-- structure forking_adversary (α T U : Type)
--   [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U] [inhabited T] :=
-- (run : oracle_comp (uniform_selecting ++ (T ↦ₒ U)) α)
-- (cf : α × query_cache (T ↦ₒ U) → option T)

-- namespace forking_adversary

-- section accepting_exp

-- /-- Accepting experiment just runs the adversary returning the output and random oracle cache. -/
-- noncomputable def accepting_experiment (adv : forking_adversary α T U) :
--   oracle_comp uniform_selecting (α × query_cache (T ↦ₒ U)) :=
-- do {
--   ⟨x, ⟨log, cache⟩⟩ ← simulate (logging_oracle _ ++ₛ (random_oracle)) adv.run (∅, ∅),
--   return (x, cache)
-- }

-- /-- `accepting_experiment` succeeds if the adversary successfully chooses a fork on the output. -/
-- noncomputable def accepting_probability (adv : forking_adversary α T U) :=
-- ⁅λ out, (adv.cf out).is_some | adv.accepting_experiment⁆

-- end accepting_exp

-- section forking_exp

-- /-- Run the adversary normally, and then drop the query result for the adversarie's chosen query,
-- returning the results and final query caches of both executions. -/
-- noncomputable def forking_experiment (adv : forking_adversary α T U) :
--   oracle_comp uniform_selecting ((α × query_cache (T ↦ₒ U)) × (α × query_cache (T ↦ₒ U))) :=
-- do {
--   ⟨x, ⟨log₁, cache₁⟩⟩ ← simulate (logging_oracle _ ++ₛ random_oracle) adv.run (∅, ∅),

--   cache₁' ← return (cache₁.drop_query () ((adv.cf (x, cache₁)).get_or_else default)),

--   ⟨x', ⟨log₂, cache₂⟩⟩ ← simulate (seeded_oracle _ ++ₛ random_oracle) adv.run (log₁, cache₁'),

--   return ((x, cache₁), (x', cache₂))
-- }

-- /-- `forking_experiment` succeeds if the first run successfully chooses a query to fork,
-- and the second run chooses the same query afterwords. -/
-- def accept_fork (adv : forking_adversary α T U)
--   (out : (α × query_cache (T ↦ₒ U)) × (α × query_cache (T ↦ₒ U))) : Prop :=
-- (adv.cf out.1).is_some ∧
--   (adv.cf out.1) = (adv.cf out.2)

-- def cache_differs (adv : forking_adversary α T U)
--   (out : (α × query_cache (T ↦ₒ U)) × (α × query_cache (T ↦ₒ U))) : Prop :=
-- out.1.2.lookup () ((adv.cf out.1).get_or_else default) ≠
--   out.2.2.lookup () ((adv.cf out.1).get_or_else default)

-- /-- `forking_probability` is the probability of both succeeding via `accept_fork`,
-- and getting different cache outputs at the chosen query being fork. -/
-- noncomputable def forking_probability (adv : forking_adversary α T U) :=
-- ⁅λ out, adv.accept_fork out ∧ adv.cache_differs out | adv.forking_experiment⁆

-- end forking_exp

-- section success_probs

-- variable [fintype T]
-- variables (adv : forking_adversary α T U)

-- lemma pow_two_accepting_probability_le_prob_event_accept_fork :
--   (adv.accepting_probability) ^ 2 / fintype.card T ≤
--     ⁅adv.accept_fork | adv.forking_experiment⁆ :=
-- calc (adv.accepting_probability) ^ 2 / fintype.card T =
--   ⁅λ out, (adv.cf out).is_some | adv.accepting_experiment⁆ ^ 2 / fintype.card T : rfl
--   ... = (∑' t, ⁅= some t | adv.cf <$> adv.accepting_experiment⁆) ^ 2 / fintype.card T :
--     by rw [prob_event_is_some']
--   ... = (∑ t, ⁅= some t | adv.cf <$> adv.accepting_experiment⁆) ^ 2 / fintype.card T :
--     congr_arg (λ y, y ^ 2 / (fintype.card T : ℝ≥0∞))
--       (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))
--   ... ≤ ∑ t, ⁅= some t | adv.cf <$> adv.accepting_experiment⁆ ^ 2 :
--     by simpa [one_add_one_eq_two] using ennreal.pow_sum_div_card_le_sum_pow
--       (finset.univ : finset T) (λ t, ⁅= some t | adv.cf <$> adv.accepting_experiment⁆)
--         (λ _ _, prob_output_ne_top _ _) 1
--   ... = ∑' t, ⁅= some t | adv.cf <$> adv.accepting_experiment⁆ ^ 2 :
--     symm (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))

--   ... = ∑' t, ⁅= (some t, some t) | adv.cf <$> adv.accepting_experiment ×ₘ adv.cf <$> adv.accepting_experiment⁆ :
--     by simp only [pow_two, prob_output_product]

--   --------------------------------------------------------------------------------------------

--   ... = ∑' t, ⁅= (some t, some t) | prod.map adv.cf adv.cf <$> adv.forking_experiment⁆ : sorry
--   ... = ⁅λ out, out.1.is_some ∧ out.1 = out.2 | prod.map adv.cf adv.cf <$> adv.forking_experiment⁆ :
--     begin
--       sorry,
--     end
--   ... = ⁅λ out, (adv.cf out.1).is_some ∧ (adv.cf out.1 = adv.cf out.2) | adv.forking_experiment⁆ :
--     by simpa only [prob_event_map']
--   ... = ⁅adv.accept_fork | adv.forking_experiment⁆ : rfl

-- theorem forking_probability_at_least :
--   (adv.accepting_probability) ^ 2 / fintype.card T
--     - adv.accepting_probability / fintype.card U
--       ≤ adv.forking_probability :=
-- sorry


-- end success_probs

-- end forking_adversary



structure forking_adversary (α T U : Type)
  [inhabited U] [fintype U] [decidable_eq T] [decidable_eq U] [inhabited T] :=
(run : oracle_comp (uniform_selecting ++ (T ↦ₒ U)) α)
(cf : α → option T)

namespace forking_adversary

@[inline, reducible] def cf' (adv : forking_adversary α T U) :
  α × query_cache spec → option T := adv.cf ∘ prod.fst

section accepting_exp

-- #check simulate_map

/-- Accepting experiment just runs the adversary returning the output and random oracle cache. -/
noncomputable def accepting_experiment (adv : forking_adversary α T U) :
  oracle_comp uniform_selecting (α × query_cache (T ↦ₒ U)) :=
do {
  ⟨x, ⟨log, cache⟩⟩ ← simulate (logging_oracle _ ++ₛ random_oracle) adv.run (∅, ∅),
  return (x, cache)
}

/-- Write `accepting_experiment` without pattern matching / syntactic sugar. -/
lemma accepting_experiment_eq (adv : forking_adversary α T U) : adv.accepting_experiment =
  simulate (logging_oracle _ ++ₛ random_oracle) adv.run (∅, ∅) >>= λ z, return (z.1, z.2.2) :=
begin
  rw [accepting_experiment],
  refine congr_arg (λ z, _ >>= z) (funext (λ z, _)),
  rcases z with ⟨x, ⟨log, cache⟩⟩,
  refl,
end

/-- `accepting_experiment` succeeds if the adversary successfully chooses a fork on the output. -/
noncomputable def accepting_probability (adv : forking_adversary α T U) :=
⁅λ out, (adv.cf out.1).is_some | adv.accepting_experiment⁆

---

noncomputable def accepting_experiment_cf (adv : forking_adversary α T U) :
  oracle_comp uniform_selecting (option T) :=
simulate' (logging_oracle _ ++ₛ random_oracle) (adv.cf <$> adv.run) (∅, ∅)

lemma accepting_probability_eq_prob_event_is_some (adv : forking_adversary α T U) :
  adv.accepting_probability = ⁅λ out, out.is_some | adv.accepting_experiment_cf⁆ :=
begin
  rw [accepting_probability, accepting_experiment_eq],
  rw [accepting_experiment_cf, simulate'_map],
  sorry,
end

end accepting_exp

section forking_exp

/-- Run the adversary normally, and then drop the query result for the adversarie's chosen query,
returning the results and final query caches of both executions. -/
noncomputable def forking_experiment (adv : forking_adversary α T U) :
  oracle_comp uniform_selecting ((α × query_cache (T ↦ₒ U)) × (α × query_cache (T ↦ₒ U))) :=
do {
  ⟨x, ⟨log₁, cache₁⟩⟩ ← simulate (logging_oracle _ ++ₛ random_oracle)
    adv.run (∅, ∅),

  ⟨x', ⟨log₂, cache₂⟩⟩ ← simulate (seeded_oracle _ ++ₛ random_oracle)
    adv.run (log₁, (cache₁.drop_query () ((adv.cf x).get_or_else default))),

  return ((x, cache₁), (x', cache₂))
}

/-- `forking_experiment` succeeds if the first run successfully chooses a query to fork,
and the second run chooses the same query afterwords. -/
def accept_fork (adv : forking_adversary α T U)
  (out : (α × query_cache (T ↦ₒ U)) × (α × query_cache (T ↦ₒ U))) : Prop :=
(adv.cf' out.1).is_some ∧
  (adv.cf' out.1) = (adv.cf' out.2)

-- `output_differs` function or something
def cache_differs (adv : forking_adversary α T U)
  (out : (α × query_cache (T ↦ₒ U)) × (α × query_cache (T ↦ₒ U))) : Prop :=
out.1.2.lookup () ((adv.cf' out.1).get_or_else default) ≠
  out.2.2.lookup () ((adv.cf' out.1).get_or_else default)

/-- `forking_probability` is the probability of both succeeding via `accept_fork`,
and getting different cache outputs at the chosen query being fork. -/
noncomputable def forking_probability (adv : forking_adversary α T U) :=
⁅λ out, adv.accept_fork out ∧ adv.cache_differs out | adv.forking_experiment⁆

----

noncomputable def forking_experiment_cf (adv : forking_adversary α T U) :
  oracle_comp uniform_selecting (option T × option T) :=
do {
  ⟨t, ⟨log₁, cache₁⟩⟩ ← simulate (logging_oracle _ ++ₛ random_oracle) (adv.cf <$> adv.run) (∅, ∅),

  ⟨t', ⟨log₂, cache₂⟩⟩ ← simulate (seeded_oracle _ ++ₛ random_oracle)
    (adv.cf <$> adv.run) (log₁, (cache₁.drop_query () (t.get_or_else default))),

  return (t, t')
}

/-- Write `forking_experiment_cf` without pattern matching / syntactic sugar.-/
lemma forking_experiment_cf_eq (adv : forking_adversary α T U) : adv.forking_experiment_cf =
  simulate (logging_oracle _ ++ₛ random_oracle) (adv.cf <$> adv.run) (∅, ∅) >>= λ z,
  simulate (seeded_oracle _ ++ₛ random_oracle)
    (adv.cf <$> adv.run) (z.2.1, (z.2.2.drop_query () (z.1.get_or_else default))) >>= λ z',
  return (z.1, z'.1) :=
begin
  rw forking_experiment_cf,
  refine congr_arg (λ z, _ >>= z) (funext (λ z, _)),
  rcases z with ⟨x, ⟨log, cache⟩⟩,
  rw forking_experiment_cf._match_2,
  refine congr_arg (λ z, _ >>= z) (funext (λ z, _)),
  rcases z with ⟨x, ⟨log, cache⟩⟩,
  rw forking_experiment_cf._match_1
end

lemma prob_event_accept_fork_eq_tsum_prob_output (adv : forking_adversary α T U) :
  ⁅adv.accept_fork | adv.forking_experiment⁆ =
    ∑' t, ⁅= (some t, some t) | adv.forking_experiment_cf⁆ :=
sorry

end forking_exp

section success_probs

variable [fintype T]
variables (adv : forking_adversary α T U)

lemma pow_two_accepting_probability_le_prob_event_accept_fork :
  (adv.accepting_probability) ^ 2 / fintype.card T ≤
    ⁅adv.accept_fork | adv.forking_experiment⁆ :=
calc (adv.accepting_probability) ^ 2 / fintype.card T =
  ⁅λ out, out.is_some | adv.accepting_experiment_cf⁆ ^ 2 / fintype.card T :
    by rw [accepting_probability_eq_prob_event_is_some]
  ... = (∑' t, ⁅= some t | adv.accepting_experiment_cf⁆) ^ 2 / fintype.card T :
    by simp only [prob_event_is_some]
  ... = (∑ t, ⁅= some t | adv.accepting_experiment_cf⁆) ^ 2 / fintype.card T :
    congr_arg (λ y, y ^ 2 / (fintype.card T : ℝ≥0∞))
      (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))
  ... ≤ ∑ t, ⁅= some t | adv.accepting_experiment_cf⁆ ^ 2 :
    by simpa [one_add_one_eq_two] using ennreal.pow_sum_div_card_le_sum_pow
      (finset.univ : finset T) (λ t, ⁅= some t | adv.accepting_experiment_cf⁆)
        (λ _ _, prob_output_ne_top _ _) 1
  ... = ∑' t, ⁅= some t | adv.accepting_experiment_cf⁆ ^ 2 :
    symm (tsum_eq_sum (λ x hx, (hx (finset.mem_univ x)).elim))

  ... = ∑' t, ⁅= (some t, some t) | adv.accepting_experiment_cf ×ₘ adv.accepting_experiment_cf⁆ :
    by simp only [pow_two, prob_output_product]


  --------------------------------------------------------------------------------------------


  ... ≤ ∑' t, ⁅= (some t, some t) | adv.forking_experiment_cf⁆ : begin
    refine ennreal.tsum_le_tsum (λ t, _),
    simp only [accepting_experiment_cf, forking_experiment_cf_eq, product],
    sorry
  end
  ... = ⁅adv.accept_fork | adv.forking_experiment⁆ :
    by rw [prob_event_accept_fork_eq_tsum_prob_output]

theorem forking_probability_at_least :
  (adv.accepting_probability) ^ 2 / fintype.card T
    - adv.accepting_probability / fintype.card U
      ≤ adv.forking_probability :=
sorry


end success_probs

end forking_adversary
