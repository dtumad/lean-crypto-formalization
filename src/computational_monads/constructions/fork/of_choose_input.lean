/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.constructions.fork.fork

/-!
# Forking Adversaries Based on Logged Queries

This file constructs a forkable adversary from a base adversary and a function
that chooses a query given a result of the computation.
This is often more useful than the base adversary, which expects a query index
rather than the actual inputs and outputs of the queries.
Done using a simulation with a logging oracle.
-/


open_locale big_operators ennreal
open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' adv_spec exp_spec : oracle_spec} {i : spec.ι} --{q : ℕ}

namespace fork_adversary

-- TODO: for the hhs sig
section of_choose_input

open oracle_comp

def of_choose_input (adv : sec_adversary spec α β)
  (i : spec.ι) (choose_input : α → β → spec.domain i × spec.range i) :
  fork_adversary spec α (β × query_log spec) i :=
{ run := λ y, simulate loggingₛₒ (adv.run y) ∅,
  choose_fork := λ y z, let inp := choose_input y z.1 in
    if inp ∈ z.2 i then some ↑(list.index_of inp (z.2 i)) else none,
  qb := adv.qb,
  -- q_eq_bound := by simp only [query_count.get_count_increment, eq_self_iff_true, if_true],
  -- qb_is_bound := λ y, logging_oracle.queries_at_most_simulate _ _
  --   (queries_at_most_trans _ _ _ (adv.qb_is_bound y) (indexed_list.le_add_values _ _)) _
    }

variables (adv : sec_adversary spec α β)
  (choose_input : α → β → spec.domain i × spec.range i)
variable [uniform_selecting ⊂ₒ spec]

example (adv : sec_adversary spec α β)
  (choose_input : α → β → spec.domain i × spec.range i)
  [uniform_selecting ⊂ₒ spec] : sorry :=
begin
  -- have := fork (of_choose_input adv i choose_input),
  sorry,
end

-- lemma fork_success_of_choose_input (y : α) (fr : fork_result (of_choose_input adv i choose_input))
--   (hfr : fr ∈ (fork (of_choose_input adv i choose_input) y).support) : sorry := sorry



-- lemma mem_support_simulate (fr : fork_result (of_choose_input adv i choose_input)) (y : α)
--   (hfr : fr ∈ (fork (of_choose_input adv i choose_input) y).support) :
--   fr.side_output₁ ∈ (simulate seededₛₒ)

-- lemma same_fork_point_of_choose_input_iff (fr : fork_result (of_choose_input adv i choose_input)) (y : α)
--   (hfr : fr ∈ (fork (of_choose_input adv i choose_input) y).support) :
--   same_fork_point fr ↔ ∃ z z' : β,
--     (choose_input y fr.side_output₁.1 ∈ ) :=
-- begin

-- end

end of_choose_input

end fork_adversary