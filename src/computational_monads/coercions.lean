import computational_monads.uniform_select
import computational_monads.simulation_oracles

open oracle_comp oracle_comp_spec

variables (spec spec' spec'' : oracle_comp_spec) (A : Type)

instance coe_append_right :
  has_coe (oracle_comp spec A) (oracle_comp (spec ++ spec') A) :=
{ coe := λ oc, oc.simulate' (stateless_simulation_oracle spec (spec ++ spec')
      (λ i t, let i' : (spec ++ spec').ι := sum.inl i in query i' t)) () }

instance coe_append_right' [has_coe (oracle_comp spec A) (oracle_comp spec' A)] :
  has_coe (oracle_comp spec A) (oracle_comp (spec' ++ spec'') A) :=
{ coe := λ oc, ↑(oc : oracle_comp spec' A) }

instance coe_append_left :
  has_coe (oracle_comp spec A) (oracle_comp (spec' ++ spec) A) :=
{ coe := λ oc, oc.simulate' (stateless_simulation_oracle spec (spec' ++ spec)
      (λ i t, let i' : (spec' ++ spec).ι := sum.inr i in query i' t)) () }

instance coe_append_left' [has_coe (oracle_comp spec A) (oracle_comp spec' A)] :
  has_coe (oracle_comp spec A) (oracle_comp (spec'' ++ spec') A) :=
{ coe := λ oc, ↑(oc : oracle_comp spec' A) }

/-- TODO: This `coe` instance might not be really useful? should test for real use cases -/
instance coe_spec_assoc :
  has_coe (oracle_comp (spec ++ (spec' ++ spec'')) A) (oracle_comp (spec ++ spec' ++ spec'') A) :=
⟨λ oc, oc.simulate' ⟪λ i, match i with 
| (sum.inl i) :=
  λ t, let i' : (spec ++ spec' ++ spec'').ι := sum.inl (sum.inl i) in query i' t
| (sum.inr (sum.inl i)) :=
  λ t, let i' : (spec ++ spec' ++ spec'').ι := sum.inl (sum.inr i) in query i' t
| (sum.inr (sum.inr i)) := 
  λ t, let i' : (spec ++ spec' ++ spec'').ι := sum.inr i in query i' t
end⟫ ()⟩

/-- coercion makes it possible to mix computations on individual oracles -/
example {spec : oracle_comp_spec} : oracle_comp (coin_oracle ++ uniform_selecting ++ spec) bool := 
do { n ←$[0..10], if n = 0 then return ff else coin }

instance simulation_oracle.coe (spec spec' : oracle_comp_spec) :
  has_coe (simulation_oracle spec spec') (simulation_oracle spec (spec ++ spec')) :=
{ coe := λ so, {
  S := so.S,
  o := λ i x, ↑(so.o i x)
}}

instance c' (spec spec' : oracle_comp_spec) :
  has_coe (simulation_oracle spec spec') (simulation_oracle spec (spec' ++ spec)) :=
{ coe := λ so, {
  S := so.S,
  o := λ i x, ↑(so.o i x)
}}

instance c'' (spec spec' spec'' : oracle_comp_spec) :
  has_coe (simulation_oracle spec spec') (simulation_oracle spec (spec' ++ spec'')) :=
{ coe := λ so, {
  S := so.S,
  o := λ i x, ↑(so.o i x)
}}

instance c''' (spec spec' spec'' : oracle_comp_spec) :
  has_coe (simulation_oracle spec spec') (simulation_oracle spec (spec'' ++ spec')) :=
{ coe := λ so, {
  S := so.S,
  o := λ i x, ↑(so.o i x)
}}

noncomputable example {A B C D : Type} [fintype C] [inhabited C] [decidable_eq C] :
  simulation_oracle ((A →ₒ C) ++ (unit →ₒ C))
    ((A →ₒ B) ++ (B →ₒ C) ++ uniform_selecting) :=
simulation_oracle_append _ _ _
  ↑(stateless_simulation_oracle (A →ₒ C) ((A →ₒ B) ++ (B →ₒ C))
    (λ i a, do {
      b ← query (sum.inl ()) a,
      c ← query (sum.inr ()) b,
      return c
  }))
  ↑(random_simulation_oracle (unit →ₒ C))
