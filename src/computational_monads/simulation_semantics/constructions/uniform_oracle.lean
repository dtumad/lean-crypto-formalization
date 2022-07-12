import computational_monads.simulation_semantics.constructions.stateless_oracle

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}
  (oa : oracle_comp spec A)

noncomputable def uniform_oracle (spec : oracle_spec) [spec.finite_range] : 
  simulation_oracle spec uniform_selecting :=
⟪ λ i t, $ᵗ (spec.range i) ⟫

@[simp]
lemma default_state_uniform_oracle (spec : oracle_spec) [spec.finite_range] :
  (uniform_oracle spec).default_state = () := rfl

@[simp]
lemma uniform_oracle_apply (spec : oracle_spec) (i : spec.ι) (t : spec.domain i) [spec.finite_range] (s : unit) :
  (uniform_oracle spec).o i (t, s) = $ᵗ (spec.range i) >>= λ u, return (u, ()) := rfl
