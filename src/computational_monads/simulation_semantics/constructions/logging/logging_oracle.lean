import computational_monads.simulation_semantics.constructions.logging.query_log.basic
import computational_monads.simulation_semantics.constructions.tracking_oracle

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} 
  
def logging_oracle (spec : oracle_spec) [spec.computable] :
  sim_oracle spec spec (query_log spec) :=
⟪ query | λ i t u, query_log.log_query i t u, query_log.init spec ⟫

namespace logging_oracle

variables (log : query_log spec) (log' : query_log spec')
variable [spec.computable]

@[simp]
lemma apply (i : spec.ι) (t : spec.domain i) :
  (logging_oracle spec) i (t, log) = query i t >>= λ u, return (u, log.log_query i t u) := rfl

section simulate

@[simp]
lemma simulate_pure (a : α) : simulate (logging_oracle _) (return a) log = return ⟨a, log⟩ := rfl

@[simp]
lemma simulate_query (i : spec.ι) (t : spec.domain i) :
  simulate (logging_oracle _) (query i t) log =
    do { u ← query i t, return (u, log.log_query i t u) } := rfl

@[simp]
lemma simulate_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  simulate (logging_oracle _) (oa >>= ob) log =
    (simulate (logging_oracle _) oa log) >>=
      (λ x, simulate (logging_oracle _) (ob x.1) x.2) := rfl

end simulate

section distribution_semantics

open distribution_semantics

section eval_dist

variable [spec.finite_range]

/-- If you throw outf final state then it looks like the original computation -/
@[simp]
lemma eval_dist_simulate'_equiv (oa : oracle_comp spec α) :
  simulate' (logging_oracle spec) oa log ≃ₚ oa :=
tracking_oracle.eval_dist_simulate'_query_eq_eval_dist _ _ oa log

@[simp]
lemma eval_dist_default_simulate'_equiv (oa : oracle_comp spec α) :
  default_simulate' (logging_oracle spec) oa ≃ₚ oa :=
eval_dist_simulate'_equiv (query_log.init spec) oa

end eval_dist

end distribution_semantics

end logging_oracle