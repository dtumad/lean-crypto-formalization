import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.simulation_oracles
import computational_monads.simulation_semantics.constructions.query_log
import computational_monads.distribution_semantics.equiv

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

section logging_oracle

/-- Extend the state of a simulation oracle to also track the inputs and outputs of queries.
  The actual oracle calls are forwarded directly to the original oracle. -/
def logging_oracle (spec : oracle_spec) [spec.computable] : 
  simulation_oracle spec spec :=
{ S := query_log spec,
  default_state := query_log.init spec,
  o := λ i ⟨t, log⟩, do { u ← query i t, return (u, log.log_query i t u) } }

@[simp]
lemma default_state_logging_oracle (spec : oracle_spec) [spec.computable] :
  (logging_oracle spec).default_state = query_log.init spec := rfl

@[simp]
lemma logging_oracle_apply [spec.computable] (i : spec.ι) (t : spec.domain i) (log : query_log spec) :
  (logging_oracle spec).o i (t, log) = query i t >>= λ u, return (u, log.log_query i t u) := rfl

namespace logging_oracle

@[simp]
lemma simulate_pure [spec.computable] (a : A) (log : query_log spec) :
  simulate (logging_oracle _) (return a) log = return ⟨a, log⟩ :=
rfl

@[simp]
lemma simulate_query [spec.computable] (i : spec.ι) (t : spec.domain i) (log : query_log spec) :
  simulate (logging_oracle _) (query i t) log =
    do { u ← query i t, return (u, log.log_query i t u) } :=
rfl

@[simp]
lemma simulate_bind [spec.computable] (oa : oracle_comp spec A)
  (ob : A → oracle_comp spec B) (log : query_log spec) :
  simulate (logging_oracle _) (oa >>= ob) log =
    (simulate (logging_oracle _) oa log) >>=
      (λ x, simulate (logging_oracle _) (ob x.1) x.2) :=
rfl

@[simp]
lemma eval_distribution_simulate' [spec.computable] [spec.finite_range]
  (oa : oracle_comp spec A) (log : query_log spec) :
  ⟦ simulate' (logging_oracle _) oa log ⟧ = ⟦ oa ⟧ :=
begin
  induction oa with A a A B oa ob hoa hob i t,
  {
    simp [pmf.pure_map],
  },
  {
    rw [bind'_eq_bind],
    rw [eval_distribution_simulate'_bind],
    rw [eval_distribution_bind], sorry,
  },
  {
    rw [eval_distribution_simulate'_query],
    rw [logging_oracle_apply],
    rw [eval_distribution_bind],
    rw [pmf.bind_map],
    simp [pmf.bind_map, functor.map, pmf.bind_pure],
    refine pmf.bind_pure _,
  }
end

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

section caching_oracle

def caching_oracle (spec : oracle_spec) [spec.computable] :
  simulation_oracle spec spec :=
{ S := query_log spec,
  default_state := query_log.init spec,
  o := λ i ⟨t, log⟩, match log.lookup i t with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do { u ← query i t, return (u, log.log_query i t u) }
  end }

@[simp]
lemma default_state_caching_oracle (spec : oracle_spec) [spec.computable] :
  (caching_oracle spec).default_state = query_log.init spec := rfl

end caching_oracle

section random_oracle

/-- Oracle that responds uniformly at random to any new queries,
  but returns the same result to subsequent oracle queries -/
noncomputable def random_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] :
  simulation_oracle spec uniform_selecting :=
(uniform_oracle spec) ∘ₛ (caching_oracle spec)

@[simp]
lemma default_state_random_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] :
  (random_oracle spec).default_state = (query_log.init spec, ()) := rfl

end random_oracle