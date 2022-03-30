import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate

-- TODO: maybe e.g. `stateless_simulation_oracle` → `stateless_oracle`. No confusion with e.g. `stateless_oracle_spec`

open oracle_comp oracle_spec

variables {spec spec' : oracle_spec}

section stateless_oracles

def stateless_simulation_oracle (spec spec' : oracle_spec)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)) :
  simulation_oracle spec spec' :=
{ S := unit,
  o := λ i ⟨t, _⟩, o i t >>= λ u, return (u, ()) }

notation `⟪` o `⟫` := stateless_simulation_oracle _ _ o

variable (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))

@[simp]
lemma stateless_oracle_apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  ⟪o⟫.o i (t, s) = o i t >>= λ u, return (u, ()) := rfl

section identity_oracle

def identity_oracle (spec : oracle_spec) : simulation_oracle spec spec :=
⟪ query ⟫

@[simp]
lemma identity_oracle_apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  (identity_oracle spec).o i (t, s) = query i t >>= λ u, return (u, ()) := rfl

end identity_oracle

section random_oracle

noncomputable def random_simulation_oracle (spec : oracle_spec) [spec.computable] [spec.finite_range] : 
  simulation_oracle spec uniform_selecting :=
⟪ λ i t, uniform_select_fintype ⟫

end random_oracle

end stateless_oracles