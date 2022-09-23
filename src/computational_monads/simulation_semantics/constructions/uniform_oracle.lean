import computational_monads.simulation_semantics.constructions.stateless_oracle
import computational_monads.constructions.uniform_select

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}

@[simps]
noncomputable def uniform_oracle (spec : oracle_spec) [spec.finite_range] : 
  simulation_oracle spec uniform_selecting :=
⟪λ i t, $ᵗ (spec.range i)⟫

namespace uniform_oracle

variables (oa : oracle_comp spec A)
variable [spec.finite_range]

noncomputable instance S_unique : unique (uniform_oracle spec).S := stateless_oracle.S_unique _

@[simp]
lemma apply_eq (i : spec.ι) (t : spec.domain i) (u : unit) :
  (uniform_oracle spec).o i (t, u) = $ᵗ (spec.range i) >>= λ u, return (u, ()) := rfl

@[simp]
lemma support_apply (i : spec.ι) (t : spec.domain i) (u : unit) :
  ((uniform_oracle spec).o i (t, u)).support = ⊤ :=
by simp only [set.eq_univ_iff_forall, apply_eq, support_bind, support_uniform_select_fintype,
  set.top_eq_univ, support_pure, set.Union_true, set.Union_singleton_eq_range, set.mem_range,
  prod.forall, prod.mk.inj_iff, exists_eq_left, forall_const, eq_iff_true_of_subsingleton]



section eval_dist


end eval_dist

end uniform_oracle