import computational_monads.distribution_semantics.eval_distribution
import to_mathlib.pmf_stuff

/-!
# Equivalence Between Computations in Terms of Distribution Semantics

Introduces the notation `oa ≃ₚ oa'` for two computations with the same associated distribution.

Also general lemmas about computations that are equivalent in terms of distribution.
It is often simpler to work with this than distributions directly, particularly because the
  original computations have an induction principle that a general `pmf` doesn't have.
-/

variables {α β γ : Type} {spec spec' : oracle_spec}
variable [spec.finite_range]
variable [spec'.finite_range]

namespace distribution_semantics

-- Notation for two computations that are equivalent under `eval_distribution`
notation oa `≃ₚ` oa' := ⦃oa⦄ = ⦃oa'⦄

lemma support_eq_of_equiv {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') : oa.support = oa'.support :=
by simp_rw [← support_eval_distribution, h]

lemma congr_equiv {oa oa' : oracle_comp spec α} (h : oa = oa') : oa ≃ₚ oa' :=
congr_arg eval_distribution h

variables  (oa : oracle_comp spec α) (oa' : oracle_comp spec' α)
  (ob : α → oracle_comp spec β) (ob' : α → oracle_comp spec' β)

section bind

@[simp]
lemma pure_bind_equiv (a : α) : (pure a >>= ob) ≃ₚ (ob a) :=
(eval_distribution_bind (return a) ob).trans (pmf.pure_bind a (λ a, ⦃ob a⦄))

@[simp]
lemma bind_pure_equiv : (oa >>= pure) ≃ₚ oa :=
trans (eval_distribution_bind oa pure) (pmf.bind_pure (⦃oa⦄))

lemma bind_equiv_of_equiv_first {oa oa' : oracle_comp spec α} (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
by simp_rw [eval_distribution_bind, h]

lemma bind_equiv_of_equiv_second (oa : oracle_comp spec α) {ob ob' : α → oracle_comp spec β}
  (h : ∀ a, (ob a) ≃ₚ (ob' a)) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
by simp_rw [eval_distribution_bind, h]

lemma bind_equiv_of_equiv_of_equiv {oa oa' : oracle_comp spec α} {ob ob' : α → oracle_comp spec β}
  (h : oa ≃ₚ oa') (h' :∀ a, (ob a) ≃ₚ (ob' a)) : (oa >>= ob) ≃ₚ (oa' >>= ob') :=
calc oa >>= ob ≃ₚ oa' >>= ob : bind_equiv_of_equiv_first ob h
  ... ≃ₚ oa' >>= ob' : bind_equiv_of_equiv_second oa' h'

@[simp]
lemma bind_equiv_of_first_unused (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  oa >>= (λ _, ob) ≃ₚ ob :=
(eval_distribution_bind oa _).trans (pmf.bind_const ⦃oa⦄ ⦃ob⦄)

@[simp]
lemma bind_bind_equiv_of_second_unused (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (oc : α → oracle_comp spec γ) :
  (oa >>= λ a, (ob a >>= λ b, oc a)) ≃ₚ oa >>= oc :=
bind_equiv_of_equiv_second oa (λ a, bind_equiv_of_first_unused (ob a) _)

end bind

section map

variables (f : α → β)

@[simp]
lemma map_return_equiv (a : α) : f <$> (pure a : oracle_comp spec α) ≃ₚ
  (return (f a) : oracle_comp spec β) :=
trans (eval_distribution_map (pure a) f) (pmf.pure_map f a)

@[simp]
lemma bind_map_equiv (ob : β → oracle_comp spec γ) : (f <$> oa) >>= ob ≃ₚ oa >>= (ob ∘ f) :=
begin
  simp only [eval_distribution_bind, eval_distribution_map, function.comp_app],
  refine ⦃oa⦄.bind_map f (λ b, ⦃ob b⦄)
end

@[simp]
lemma map_bind_equiv (f : β → γ) : f <$> (oa >>= ob) ≃ₚ oa >>= λ a, f <$> (ob a) :=
begin
  simp only [eval_distribution_bind, functor.map, oracle_comp.bind'_eq_bind,
    function.comp_app, eval_distribution_return],
  exact ⦃oa⦄.map_bind (λ b, ⦃ob b⦄) f,
end

@[simp]
lemma map_id_equiv : id <$> oa ≃ₚ oa :=
(eval_distribution_bind oa _).trans (pmf.bind_pure ⦃oa⦄)

lemma map_equiv_of_equiv {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') : f <$> oa ≃ₚ f <$> oa' :=
by rw [eval_distribution_map, eval_distribution_map, h]

@[simp]
lemma map_map_equiv (oa : oracle_comp spec α) (f : α → β) (g : β → γ) :
  g <$> (f <$> oa) ≃ₚ (g ∘ f) <$> oa :=
calc ⦃g <$> (f <$> oa)⦄
  = pmf.map g (pmf.map f ⦃oa⦄) : by simp_rw [eval_distribution_map]
  ... = pmf.map (g ∘ f) ⦃oa⦄ : pmf.map_comp f ⦃oa⦄ g
  ... = ⦃(g ∘ f) <$> oa⦄ : symm (eval_distribution_map oa $ g ∘ f)

lemma map_map_return_equiv (a : α) (f : α → β) (g : β → γ) :
  g <$> (f <$> (return a : oracle_comp spec α)) ≃ₚ (pure (g (f a)) : oracle_comp spec γ) :=
by rw [map_map_equiv, map_return_equiv]

end map

section prod

variables (f : α → β) (g : α → γ)

@[simp]
lemma fst_map_bind_mk_equiv :
  (prod.fst <$> (oa >>= λ a, pure (f a, g a)) : oracle_comp spec β) ≃ₚ f <$> oa :=
by simp only [functor.map, oracle_comp.bind'_eq_bind, eval_distribution_bind,
  eval_distribution_return, pmf.bind_bind, pmf.pure_bind]

@[simp]
lemma snd_map_bind_mk_equiv :
  (prod.snd <$> (oa >>= λ a, pure (f a, g a)) : oracle_comp spec γ) ≃ₚ g <$> oa :=
by simp only [functor.map, oracle_comp.bind'_eq_bind, eval_distribution_bind,
  eval_distribution_return, pmf.bind_bind, pmf.pure_bind]

end prod

end distribution_semantics