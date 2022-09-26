import computational_monads.simulation_semantics.constructions.logging.caching_oracle
import computational_monads.simulation_semantics.constructions.uniform_oracle
import computational_monads.simulation_semantics.mask_state

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

/-- Oracle that responds uniformly at random to any new queries,
but returns the same result to subsequent oracle queries.
Masking is used to hide the irrelevent state of the `uniform_oracle` -/
noncomputable def random_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] :
  sim_oracle spec uniform_selecting (query_log spec) :=
((uniform_oracle spec) ∘ₛ (caching_oracle spec)).mask_state (equiv.prod_punit (query_log spec))

namespace random_oracle

variable [spec.computable]
variable [spec.finite_range]
variables (log : query_log spec) (log' : query_log spec')

/-- The support of apply is things where the log doesn't change on things previously queried,
  and the log has the new query if it was previously queried -/
lemma support_apply (i : spec.ι) (t : spec.domain i) (log : query_log spec) :
  ((random_oracle spec) i (t, log)).support =
    λ ⟨u, log'⟩, if log.lookup i t = u then log' = log else log' = log.log_query i t u :=
begin
  sorry
end

lemma support_simulate (oa : oracle_comp spec α) :
  (simulate (random_oracle spec) oa (query_log.init spec)).support = 
    {x | sorry} :=
begin
  sorry
end 

section distribution_semantics


end distribution_semantics

end random_oracle