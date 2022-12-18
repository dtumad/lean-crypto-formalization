/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.query_log.lookup
import computational_monads.simulation_semantics.constructions.logging.query_log.fork

/-!
# Seeded Simulation Oracle

This file constructs a simulation oracle that allows for a set of predetermined query responses.
The oracle takes a `query_log` as an initial state, and uses the internal values
  to respond to queries, and then forwards any additional queries back to the original oracle.
Note that if any query fails to find a seed value, the entire `query_log` is discarded,
  regardless of if further values exist for oracles of different indices.

This can more generally be thought of as a form of small-step semantics for `oracle_comp`,
  evaluating the computation using the provided value, eventually reducing to a single value,
  unless it runs out of "gas", leading to only a partial evaluation.

-/

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {α β γ : Type}
  
/-- Use the first element of the `seed` as the query result if inputs match.
  If the query values don't match then throw away the seed as computation has diverged.
  Using this with a log from a previous computation ensures they behave identically. -/
def seeded_oracle (spec : oracle_spec) :
  sim_oracle spec spec (query_log spec) :=
{ default_state := query_log.init spec,
  o := λ i ⟨t, seed⟩, match seed.lookup_fst i t with
    -- Once the seed is empty, just keep it empty going forward
    | none := (λ u, (u, query_log.init spec)) <$> query i t
    | (some u) := return (u, seed.remove_head i)
    end }

namespace seeded_oracle

variables (log : query_log spec) (log' : query_log spec')

section simulate


end simulate

section eval_dist

-- Log and run, run from seed, return original output -> looks like just logging
lemma eval_dist_seeded_oracle_fst (oa : oracle_comp spec α) (i : spec.ι)
  (choose_fork : α → query_log spec → option ℕ) :
⁅do{ ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
      seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
      ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa seed,
      return (a, log) }⁆ =
  ⁅(simulate (logging_oracle spec) oa (query_log.init spec))⁆ :=
sorry

-- Log and run, run from seed, return new output -> looks like just logging
lemma eval_dist_seeded_oracle_snd (oa : oracle_comp spec α) (i : spec.ι)
  (choose_fork : α → query_log spec → option ℕ) :
⁅do{ ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
      seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
      ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa (seed),
      return (a', log') }⁆ =  
  ⁅(simulate (logging_oracle spec) oa (query_log.init spec))⁆ :=
sorry

-- The log values match up until the point where the log was forked
lemma seeded_oracle_log_eq_log (oa : oracle_comp spec α) (i : spec.ι)
  (choose_fork : α → query_log spec → option ℕ) :
do{ ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
    seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
    ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa (seed),
    return (a, log, log') }.support
  ⊆ λ ⟨a, log, log'⟩, log.fork_cache i (choose_fork a log) =
      log'.fork_cache i (choose_fork a log) :=
sorry

end eval_dist

end seeded_oracle