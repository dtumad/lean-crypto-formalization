import computational_monads.distribution_semantics.eval_distribution
import to_mathlib.pmf_stuff

/-!
# Equivalence Between Computations in Terms of Distribution Semantics

Introduces the notation `oa ≃ₚ oa'` for two computations with the same associated distribution.

Also general lemmas about computations that are equivalent in terms of distribution.
It is often simpler to work with this than distributions directly, particularly because the
  original computations have an induction principle that a general `pmf` doesn't have.
-/

namespace distribution_semantics

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

section bind

@[simp]
lemma pure_bind_equiv (a : A) : (pure a >>= ob) ≃ₚ (ob a) :=
(eval_distribution_bind (return a) ob).trans (pmf.pure_bind a (λ a, ⦃ob a⦄))

@[simp]
lemma bind_pure_equiv : (oa >>= pure) ≃ₚ oa :=
trans (eval_distribution_bind oa pure) (pmf.bind_pure (⦃oa⦄))

lemma bind_equiv_of_equiv_first {oa oa' : oracle_comp spec A} (ob : A → oracle_comp spec B)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
by simp_rw [eval_distribution_bind, h]

lemma bind_equiv_of_equiv_second (oa : oracle_comp spec A) {ob ob' : A → oracle_comp spec B}
  (h : ∀ a, (ob a) ≃ₚ (ob' a)) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
by simp_rw [eval_distribution_bind, h]

lemma bind_equiv_of_equiv_of_equiv {oa oa' : oracle_comp spec A} {ob ob' : A → oracle_comp spec B}
  (h : oa ≃ₚ oa') (h' :∀ a, (ob a) ≃ₚ (ob' a)) : (oa >>= ob) ≃ₚ (oa' >>= ob') :=
calc oa >>= ob ≃ₚ oa' >>= ob : bind_equiv_of_equiv_first ob h
  ... ≃ₚ oa' >>= ob' : bind_equiv_of_equiv_second oa' h'

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
  simp only [eval_distribution_bind, eval_distribution_map, function.comp_app],
  refine ⦃oa⦄.bind_map f (λ b, ⦃ob b⦄)
end

@[simp]
lemma map_bind_equiv (f : B → C) : f <$> (oa >>= ob) ≃ₚ oa >>= λ a, f <$> (ob a) :=
begin
  simp only [eval_distribution_bind, functor.map, oracle_comp.bind'_eq_bind,
    function.comp_app, oracle_comp.pure'_eq_pure, eval_distribution_return],
  exact ⦃oa⦄.map_bind (λ b, ⦃ob b⦄) f,
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
calc ⦃g <$> (f <$> oa)⦄
  = pmf.map g (pmf.map f ⦃oa⦄) : by simp_rw [eval_distribution_map]
  ... = pmf.map (g ∘ f) ⦃oa⦄ : pmf.map_comp f ⦃oa⦄ g
  ... = ⦃(g ∘ f) <$> oa⦄ : symm (eval_distribution_map oa $ g ∘ f)

lemma map_map_pure_equiv (a : A) (f : A → B) (g : B → C) :
  g <$> (f <$> (pure a : oracle_comp spec A)) ≃ₚ (pure (g (f a)) : oracle_comp spec C) :=
by rw [map_map_equiv, map_pure_equiv]

@[simp]
lemma map_equiv_of_eq_id (oa : oracle_comp spec A) (f : A → A) (h : ∀ a, f a = a) :
  f <$> oa ≃ₚ oa :=
begin
  refine pmf.ext (λ a, _),
  rw [eval_distribution_map, pmf.map_apply],
  refine trans (tsum_eq_single a $ λ a' ha', _) (by simp [h]),
  simp [h a', ne.symm ha']
end

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

end distribution_semantics