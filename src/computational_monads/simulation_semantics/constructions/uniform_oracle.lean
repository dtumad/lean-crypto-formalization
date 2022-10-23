import computational_monads.simulation_semantics.constructions.stateless_oracle
import computational_monads.constructions.uniform_select

open oracle_comp oracle_spec

variables {α β : Type} {spec spec' spec'' : oracle_spec}

noncomputable def uniform_oracle (spec : oracle_spec) [spec.finite_range] : 
  sim_oracle spec uniform_selecting unit :=
⟪λ i t, $ᵗ (spec.range i)⟫

namespace uniform_oracle

variables (oa : oracle_comp spec α)
variable [spec.finite_range]

@[simp]
lemma apply_eq (i : spec.ι) (t : spec.domain i) (u : unit) :
  (uniform_oracle spec) i (t, u) = $ᵗ (spec.range i) >>= λ u, return (u, ()) := rfl

@[simp]
lemma support_apply (i : spec.ι) (t : spec.domain i) (u : unit) :
  ((uniform_oracle spec) i (t, u)).support = ⊤ :=
by simp only [set.eq_univ_iff_forall, apply_eq, support_bind, support_uniform_select_fintype,
  set.top_eq_univ, support_return, set.Union_true, set.Union_singleton_eq_range, set.mem_range,
  prod.forall, prod.mk.inj_iff, exists_eq_left, forall_const, eq_iff_true_of_subsingleton]

section eval_dist

end eval_dist

end uniform_oracle