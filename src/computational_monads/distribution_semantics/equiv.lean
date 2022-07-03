import computational_monads.distribution_semantics.prob_event

open oracle_comp oracle_spec

variables {A B C : Type} {spec spec' : oracle_spec}

variable [spec.finite_range]

-- Notation for two computations that are equivalent under `eval_distribution`
notation oa `≃ₚ` oa' := ⟦oa⟧ = ⟦oa'⟧

@[simp]
lemma pure_bind_equiv (a : A) (ob : A → oracle_comp spec B) :
  (pure a >>= ob) ≃ₚ (ob a) :=
trans (eval_distribution_bind (return a) ob) (pmf.pure_bind (λ a, ⟦ob a⟧) a)

@[simp]
lemma bind_pure_equiv (oa : oracle_comp spec A) :
  (oa >>= pure) ≃ₚ oa :=
trans (eval_distribution_bind oa pure) (pmf.bind_pure (⟦oa⟧))

@[simp]
lemma pure_map_equiv (a : A) (f : A → B) :
  f <$> (pure a : oracle_comp spec A) ≃ₚ (pure (f a) : oracle_comp spec B) :=
trans (eval_distribution_map (pure a) f) (pmf.pure_map f a)

@[simp]
lemma map_id_equiv (oa : oracle_comp spec A) :
  (λ a, a) <$> oa ≃ₚ oa :=
sorry

@[simp]
lemma fst_map_bind_mk_equiv (oa : oracle_comp spec A)
  (f : A → B) (g : A → C) :
  (prod.fst <$> (oa >>= λ a, pure (f a, g a)) : oracle_comp spec B) ≃ₚ
    f <$> oa :=
sorry

@[simp]
lemma snd_map_bind_mk_equiv (oa : oracle_comp spec A)
  (f : A → B) (g : A → C) :
  (prod.snd <$> (oa >>= λ a, pure (f a, g a)) : oracle_comp spec C) ≃ₚ
    g <$> oa :=
sorry  