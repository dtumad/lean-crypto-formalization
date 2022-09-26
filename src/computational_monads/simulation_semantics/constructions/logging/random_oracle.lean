import computational_monads.simulation_semantics.constructions.logging.caching_oracle
import computational_monads.simulation_semantics.constructions.uniform_oracle

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

/-- Mask the state value of an oracle, without changing the oracle's behaviour.
We capture this unchanged functionality by using an equivalence for the masking.
Convenient when working with composed or appended oracles, to remove unneeded state elements.
In particular `unit` state values that start spreading can be avoided.
-/
def simulation_oracle.mask_state (so : simulation_oracle spec spec' S) (mask : S ≃ S') :
  simulation_oracle spec spec' S' :=
{ default_state := mask so.default_state,
  o := λ i x, prod.map id mask <$> (so.o i $ prod.map id mask.symm x) }

/-- Oracle that responds uniformly at random to any new queries,
  but returns the same result to subsequent oracle queries -/
-- noncomputable def random_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] :
--   simulation_oracle spec uniform_selecting (query_log spec × unit) :=
-- (uniform_oracle spec) ∘ₛ (caching_oracle spec)

noncomputable def random_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] :
  simulation_oracle spec uniform_selecting (query_log spec) :=
simulation_oracle.mask_state ((uniform_oracle spec) ∘ₛ (caching_oracle spec)) (equiv.prod_punit (query_log spec))

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