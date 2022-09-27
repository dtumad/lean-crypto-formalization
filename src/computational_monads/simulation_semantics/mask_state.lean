import computational_monads.simulation_semantics.simulate

variables {α β γ : Type} {spec spec' : oracle_spec} {S S' S'' : Type}

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

namespace mask_state

variables (so : sim_oracle spec spec' S) (mask : S ≃ S') (mask' : S' ≃ S'')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (s : S) (s' : S') (x : spec.domain i × S') (y : spec.range i × S')

lemma apply_eq : so.mask_state mask i x =
  prod.map id mask <$> (so.o i $ prod.map id mask.symm x) := rfl

section support

/-- The `support` of a simulation with masked state is the same as the support without masking -/
lemma support_simulate_eq_image_support_simulate : (simulate (so.mask_state mask) oa s').support =
  (prod.map id mask) '' (simulate so oa (mask.symm s')).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { simp_rw [simulate_return, support_return, prod_map, id.def,
      set.image_singleton, equiv.apply_symm_apply] },
  {
    sorry,
  },
  { simpa only [simulate_query, apply_eq, support_map] }
end

/-- The `support` of a regular simulation can be represented as the image of a simulation
with a masked state, with the image applying an unmask function for the masking -/
lemma support_simulate_eq_preimage_support_simulate : (simulate so oa s).support =
  (prod.map id mask.symm) '' (simulate (so.mask_state mask) oa (mask s)).support :=
begin
  sorry
end

end support

end mask_state

end sim_oracle