import computational_monads.simulation_semantics.constructions.logging.query_log.basic
import computational_monads.simulation_semantics.constructions.tracking_oracle

open oracle_comp oracle_spec

variables {A B C : Type} {spec spec' spec'' : oracle_spec} 
  
@[simps]
def logging_oracle (spec : oracle_spec) [spec.computable] :
  simulation_oracle spec spec :=
⟪ query | query_log.log_query, query_log.init spec ⟫

namespace logging_oracle

variables (log : query_log spec) (log' : query_log spec')
variable [spec.computable]

@[simp]
lemma apply (i : spec.ι) (t : spec.domain i) :
  (logging_oracle spec).o i (t, log) = query i t >>= λ u, return (u, log.log_query i t u) := rfl

section simulate

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

end simulate

section eval_dist

variable [spec.finite_range]

/-- If you throw outf final state then it looks like the original computation -/
@[simp]
lemma eval_dist_simulate'_equiv (oa : oracle_comp spec A) :
  simulate' (logging_oracle spec) oa log ≃ₚ oa :=
tracking_oracle.simulate'_query_equiv_self oa query_log.log_query _ log

@[simp]
lemma eval_dist_default_simulate'_equiv (oa : oracle_comp spec A) :
  default_simulate' (logging_oracle spec) oa ≃ₚ oa :=
eval_dist_simulate'_equiv (query_log.init spec) oa

end eval_dist

end logging_oracle