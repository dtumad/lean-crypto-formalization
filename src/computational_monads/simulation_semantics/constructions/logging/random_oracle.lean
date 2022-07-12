import computational_monads.simulation_semantics.constructions.logging.caching_oracle
import computational_monads.simulation_semantics.constructions.uniform_oracle
import computational_monads.simulation_semantics.oracle_compose

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}
  (log : query_log spec) (log' : query_log spec')

/-- Oracle that responds uniformly at random to any new queries,
  but returns the same result to subsequent oracle queries -/
noncomputable def random_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] :
  simulation_oracle spec uniform_selecting :=
(uniform_oracle spec) ∘ₛ (caching_oracle spec)

@[simp]
lemma default_state_random_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] :
  (random_oracle spec).default_state = (query_log.init spec, ()) := rfl