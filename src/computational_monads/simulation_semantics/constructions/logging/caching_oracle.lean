import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.oracle_compose

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}
  (log : query_log spec) (log' : query_log spec')

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