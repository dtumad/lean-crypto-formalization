import computational_monads.distribution_semantics.prob_event

open oracle_comp oracle_spec

variables {A B C : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec A) (ob : A → oracle_comp spec B)
  (oa' : oracle_comp spec' A) (ob' : A → oracle_comp spec' B)

variable [spec.finite_range]
variable [spec'.finite_range]

-- Notation for two computations that are equivalent under `eval_distribution`
notation oa `≃ₚ` oa' := ⦃oa⦄ = ⦃oa'⦄

lemma support_eq_of_equiv {oa : oracle_comp spec A} {oa' : oracle_comp spec' A}
  (h : oa ≃ₚ oa') : oa.support = oa'.support :=
by simp_rw [← support_eval_distribution, h]

lemma prob_event_eq_of_equiv {oa : oracle_comp spec A} {oa' : oracle_comp spec' A}
  (h : oa ≃ₚ oa') (event : set A) : ⦃event | oa⦄ = ⦃event | oa'⦄ :=
by simp_rw [prob_event, h]

section bind

@[simp]
lemma pure_bind_equiv (a : A) : (pure a >>= ob) ≃ₚ (ob a) :=
(eval_distribution_bind (return a) ob).trans (pmf.pure_bind a (λ a, ⦃ob a⦄))

@[simp]
lemma prob_event_pure_bind (a : A) (event : set B) :
  ⦃event | pure a >>= ob⦄ = ⦃event | ob a⦄ :=
prob_event_eq_of_equiv (pure_bind_equiv ob a) event


------


@[simp]
lemma bind_pure_equiv : (oa >>= pure) ≃ₚ oa :=
trans (eval_distribution_bind oa pure) (pmf.bind_pure (⦃oa⦄))

@[simp]
lemma prob_event_bind_pure (event : set A) :
  ⦃event | oa >>= pure ⦄ = ⦃event | oa⦄ :=
prob_event_eq_of_equiv (bind_pure_equiv oa) event


lemma bind_equiv_of_equiv_first {oa oa' : oracle_comp spec A} (ob : A → oracle_comp spec B)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
by simp_rw [eval_distribution_bind, h]

lemma bind_equiv_of_equiv_second (oa : oracle_comp spec A) {ob ob' : A → oracle_comp spec B}
  (h : ∀ a, (ob a) ≃ₚ (ob' a)) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
by simp_rw [eval_distribution_bind, h]

@[simp]
lemma bind_equiv_of_first_unused (oa : oracle_comp spec A) (ob : oracle_comp spec B) :
  oa >>= (λ _, ob) ≃ₚ ob :=
(eval_distribution_bind oa _).trans (pmf.bind_const ⦃oa⦄ ⦃ob⦄)

@[simp]
lemma bind_bind_equiv_of_second_unused (oa : oracle_comp spec A) (ob : A → oracle_comp spec B)
  (oc : A → oracle_comp spec C) :
  (oa >>= λ a, (ob a >>= λ b, oc a)) ≃ₚ oa >>= oc :=
bind_equiv_of_equiv_second oa (λ a, bind_equiv_of_first_unused (ob a) _)

end bind

section map

variables (f : A → B)

@[simp]
lemma map_pure_equiv (a : A) : f <$> (pure a : oracle_comp spec A) ≃ₚ
  (pure (f a) : oracle_comp spec B) :=
trans (eval_distribution_map (pure a) f) (pmf.pure_map f a)

@[simp]
lemma bind_map_equiv (ob : B → oracle_comp spec C) : (f <$> oa) >>= ob ≃ₚ oa >>= (ob ∘ f) :=
begin
  sorry
end

@[simp]
lemma map_bind_equiv (f : B → C) : f <$> (oa >>= ob) ≃ₚ oa >>= λ a, f <$> (ob a) :=
begin
  simp [eval_distribution_map, eval_distribution_bind, functor.map, pmf.bind_bind],
  exact (pmf.map_bind ⦃oa⦄ _ _),
end

@[simp]
lemma map_id_equiv : id <$> oa ≃ₚ oa :=
by {simp [functor.map], exact pmf.bind_pure _} 

lemma map_equiv_of_equiv {oa : oracle_comp spec A} {oa' : oracle_comp spec' A}
  (h : oa ≃ₚ oa') : f <$> oa ≃ₚ f <$> oa' :=
by rw [eval_distribution_map, eval_distribution_map, h]

@[simp]
lemma map_map_equiv (oa : oracle_comp spec A) (f : A → B) (g : B → C) :
  g <$> (f <$> oa) ≃ₚ (g ∘ f) <$> oa :=
sorry

@[simp]
lemma map_equiv_of_eq_id (oa : oracle_comp spec A) (f : A → A) (h : ∀ a, f a = a) :
  f <$> oa ≃ₚ oa :=
sorry

end map

section prod

variables (f : A → B) (g : A → C)

@[simp]
lemma fst_map_bind_mk_equiv :
  (prod.fst <$> (oa >>= λ a, pure (f a, g a)) : oracle_comp spec B) ≃ₚ
    f <$> oa :=
by { simp [pmf.map], refl }

@[simp]
lemma snd_map_bind_mk_equiv :
  (prod.snd <$> (oa >>= λ a, pure (f a, g a)) : oracle_comp spec C) ≃ₚ
    g <$> oa :=
by { simp [pmf.map], refl }

end prod