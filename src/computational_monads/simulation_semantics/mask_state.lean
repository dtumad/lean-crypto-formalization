import computational_monads.simulation_semantics.default_simulate

variables {α β γ : Type} {spec spec' : oracle_spec} {S S' : Type}

open oracle_comp oracle_spec

namespace sim_oracle

/-- Mask the state value of an oracle, without changing the oracle's behaviour.
We capture this unchanged functionality by using an equivalence for the masking.
Convenient when working with composed or appended oracles, to remove unneeded state elements.
In particular `unit` state values that start spreading can be avoided.
-/
def mask_state (so : sim_oracle spec spec' S) (mask : S ≃ S') :
  sim_oracle spec spec' S' :=
{ default_state := mask so.default_state,
  o := λ i x, prod.map id mask <$> (so.o i $ prod.map id mask.symm x) }

end sim_oracle