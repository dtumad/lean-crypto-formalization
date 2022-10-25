import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.query_log.lookup
import computational_monads.simulation_semantics.oracle_compose

open oracle_comp oracle_spec

variables {α β γ : Type} {spec : oracle_spec} [computable spec]

/-- Oracle for logging previous queries, and returning the same value for matching inputs -/
def caching_oracle (spec : oracle_spec) [spec.computable] :
  sim_oracle spec spec (query_log spec) :=
{ default_state := query_log.init spec,
  o := λ i ⟨t, log⟩, match log.lookup i t with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do {u ← query i t, return (u, log.log_query i t u)}
  end }

namespace caching_oracle

variables (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (log : query_log spec)

@[simp] lemma apply_eq : (caching_oracle spec).o i (t, log) = option.rec_on (log.lookup i t)
  (query i t >>= λ u, return (u, log.log_query i t u)) (λ u, return (u, log)) :=
begin
  simp only [caching_oracle],
  induction log.lookup i t; refl,
end

lemma apply_eq_of_not_queried (hlog : log.not_queried i t) :
  (caching_oracle spec).o i (t, log) = (query i t >>= λ u, return (u, log.log_query i t u)) :=
begin
  sorry
end

section support



end support

section eval_dist


end eval_dist

end caching_oracle