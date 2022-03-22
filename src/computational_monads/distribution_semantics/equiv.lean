import computational_monads.distribution_semantics.eval_distribution

open oracle_comp oracle_comp_spec

variables {A B : Type}

-- Equivalence of two computations under distribution semantics
notation oa `≃ₚ` oa' := ⟦oa⟧ = ⟦oa'⟧

@[simp]
lemma bind'_pure'_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A : Type} (ca : oracle_comp spec A) :
  (bind' A A ca (pure' A)) ≃ₚ ca :=
begin
  simp,
  exact pmf.bind_pure ⟦ca⟧,
end

@[simp]
lemma bind_return_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A : Type} (ca : oracle_comp spec A) :
  (ca >>= return) ≃ₚ ca :=
bind'_pure'_equiv ca

@[simp]
lemma pure'_bind'_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A B : Type} (a : A) (cb : A → oracle_comp spec B) :
  (bind' A B (pure' A a) cb) ≃ₚ cb a :=
begin
  simp,
  exact pmf.pure_bind (eval_distribution ∘ cb) a,
end

@[simp]
lemma return_bind_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A B : Type} (a : A) (cb : A → oracle_comp spec B) :
  (return a >>= cb) ≃ₚ cb a :=
pure'_bind'_equiv a cb
