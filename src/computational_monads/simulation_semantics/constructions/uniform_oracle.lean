import computational_monads.simulation_semantics.constructions.stateless_oracle
import computational_monads.constructions.uniform_select

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}

@[simps]
noncomputable def uniform_oracle (spec : oracle_spec) [spec.finite_range] : 
  simulation_oracle spec uniform_selecting :=
⟪ λ i t, $ᵗ (spec.range i) ⟫

namespace uniform_oracle

variables (oa : oracle_comp spec A)

@[simp]
lemma uniform_oracle_apply (spec : oracle_spec) (i : spec.ι) (t : spec.domain i) [spec.finite_range] (s : unit) :
  (uniform_oracle spec).o i (t, s) = $ᵗ (spec.range i) >>= λ u, return (u, ()) := rfl

section simulate


end simulate

section eval_distribution


end eval_distribution

end uniform_oracle