import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.query_log.lookup
import computational_monads.simulation_semantics.oracle_compose

open oracle_comp oracle_spec

variables {A B C : Type} {spec spec' spec'' : oracle_spec}

def caching_oracle (spec : oracle_spec) [spec.computable] :
  sim_oracle spec spec (query_log spec) :=
{ default_state := query_log.init spec,
  o := λ i ⟨t, log⟩, match log.lookup i t with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do { u ← query i t, return (u, log.log_query i t u) }
  end }

namespace caching_oracle

variables (log : query_log spec) (log' : query_log spec')

section simulate


end simulate

section eval_dist


end eval_dist

end caching_oracle