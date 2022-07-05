import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.constructions.logging.query_log
import computational_monads.distribution_semantics.equiv

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}
  (log : query_log spec) (log' : query_log spec')

section logging_oracle

def logging_oracle (spec : oracle_spec) [spec.computable] :
  simulation_oracle spec spec :=
⟪ query | query_log.log_query, query_log.init spec ⟫

@[simp]
lemma default_state_logging_oracle (spec : oracle_spec) [spec.computable] :
  (logging_oracle spec).default_state = query_log.init spec := rfl

variable [spec.computable]

@[simp]
lemma logging_oracle_apply (i : spec.ι) (t : spec.domain i) :
  (logging_oracle spec).o i (t, log) = query i t >>= λ u, return (u, log.log_query i t u) := rfl

namespace logging_oracle

@[simp]
lemma simulate_pure (a : A) :
  simulate (logging_oracle _) (return a) log = return ⟨a, log⟩ :=
rfl

@[simp]
lemma simulate_query (i : spec.ι) (t : spec.domain i) :
  simulate (logging_oracle _) (query i t) log =
    do { u ← query i t, return (u, log.log_query i t u) } :=
rfl

@[simp]
lemma simulate_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) :
  simulate (logging_oracle _) (oa >>= ob) log =
    (simulate (logging_oracle _) oa log) >>=
      (λ x, simulate (logging_oracle _) (ob x.1) x.2) :=
rfl

section eval_distribution

variable [spec.finite_range]

/-- If you throw outf final state then it looks like the original computation -/
@[simp]
lemma eval_distribution_simulate'_equiv (oa : oracle_comp spec A) :
  simulate' (logging_oracle spec) oa log ≃ₚ oa :=
simulate'_tracking_oracle_query_equiv oa (query_log.init spec) query_log.log_query log

@[simp]
lemma eval_distribution_default_simulate'_equiv (oa : oracle_comp spec A) :
  default_simulate' (logging_oracle spec) oa ≃ₚ oa :=
eval_distribution_simulate'_equiv (query_log.init spec) oa

end eval_distribution

end logging_oracle

end logging_oracle

section seeded_oracle

/-- Use the first element of the `seed` as the query result if inputs match.
  If the query values don't match then throw away the seed as computation has diverged.
  Using this with a log from a previous computation ensures they behave identically. -/
def seeded_oracle (spec : oracle_spec) [computable spec] :
  simulation_oracle spec spec :=
{ S := query_log spec,
  default_state := query_log.init spec,
  o := λ i ⟨t, seed⟩, match seed.lookup_fst i t with
    | none := (λ u, (u, query_log.init spec)) <$> query i t
    | (some u) := return (u, seed.remove_head i)
    end }

@[simp]
lemma default_state_seeded_oracle (spec : oracle_spec) [spec.computable] :
  (seeded_oracle spec).default_state = query_log.init spec := rfl

-- Log and run, run from seed, return original output -> looks like just logging
lemma seeded_oracle_first_equiv (spec : oracle_spec) [spec.computable] [spec.finite_range]
  (oa : oracle_comp spec A) (i : spec.ι) (choose_fork : A → query_log spec → option ℕ) :
⟦(do {
  ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
  seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
  ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa seed,
  return (a, log)
} : oracle_comp spec (A × query_log spec))⟧ =
  ⟦(simulate (logging_oracle spec) oa (query_log.init spec))⟧ :=
sorry

-- Log and run, run from seed, return new output -> looks like just logging
lemma seeded_oracle_second_equiv (spec : oracle_spec) [spec.computable] [spec.finite_range]
  (oa : oracle_comp spec A) (i : spec.ι) (choose_fork : A → query_log spec → option ℕ) :
⟦(do {
  ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
  seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
  ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa (seed),
  return (a', log')
} : oracle_comp spec (A × query_log spec))⟧ =  
  ⟦(simulate (logging_oracle spec) oa (query_log.init spec))⟧ :=
sorry

-- The log values match up until the point where the log was forked
lemma seeded_oracle_log_eq_log (spec : oracle_spec) [spec.computable] [spec.finite_range]
  (oa : oracle_comp spec A) (i : spec.ι) (choose_fork : A → query_log spec → option ℕ) :
(do {
  ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
  seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
  ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa (seed),
  return (a, log, log')
} : oracle_comp spec (A × query_log spec × query_log spec)).support
  ⊆ λ ⟨a, log, log'⟩, log.fork_cache i (choose_fork a log) =
    log'.fork_cache i (choose_fork a log) :=
sorry

end seeded_oracle