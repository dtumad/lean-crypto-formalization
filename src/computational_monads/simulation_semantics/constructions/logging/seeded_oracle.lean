import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.query_log.lookup
import computational_monads.simulation_semantics.constructions.logging.query_log.fork

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}
  (log : query_log spec) (log' : query_log spec')
variable [spec.computable]

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
lemma seeded_oracle_first_equiv [spec.finite_range]
  (oa : oracle_comp spec A) (i : spec.ι) (choose_fork : A → query_log spec → option ℕ) :
⦃(do {
  ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
  seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
  ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa seed,
  return (a, log)
} : oracle_comp spec (A × query_log spec))⦄ =
  ⦃(simulate (logging_oracle spec) oa (query_log.init spec))⦄ :=
sorry

-- Log and run, run from seed, return new output -> looks like just logging
lemma seeded_oracle_second_equiv [spec.finite_range]
  (oa : oracle_comp spec A) (i : spec.ι) (choose_fork : A → query_log spec → option ℕ) :
⦃(do {
  ⟨a, log⟩ ← simulate (logging_oracle spec) oa (query_log.init spec),
  seed ← return (log.fork_cache i $ choose_fork a log).to_seed,
  ⟨a', log'⟩ ← simulate (seeded_oracle spec) oa (seed),
  return (a', log')
} : oracle_comp spec (A × query_log spec))⦄ =  
  ⦃(simulate (logging_oracle spec) oa (query_log.init spec))⦄ :=
sorry

-- The log values match up until the point where the log was forked
lemma seeded_oracle_log_eq_log [spec.finite_range]
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