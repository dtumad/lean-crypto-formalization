/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.eval_dist

/-!
# Equivalence Between Computations in Terms of Distribution Semantics

Introduces the notation `oa ≃ₚ oa'` for two computations with the same associated distribution.

Also general lemmas about computations that are equivalent in terms of distribution.
It is often simpler to work with this than distributions directly, particularly because the
  original computations have an induction principle that a general `pmf` doesn't have.
-/

namespace distribution_semantics

open oracle_comp oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} [finite_range spec] [finite_range spec']

-- Notation for two computations that are equivalent under `eval_dist`
notation oa ` ≃ₚ ` oa' := ⦃oa⦄ = ⦃oa'⦄

lemma support_eq_of_equiv {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') : oa.support = oa'.support :=
by simp_rw [← support_eval_dist, h]

lemma congr_equiv {oa oa' : oracle_comp spec α} (h : oa = oa') : oa ≃ₚ oa' :=
congr_arg eval_dist h

variables  (oa : oracle_comp spec α) (oa' : oracle_comp spec' α)
  (ob : α → oracle_comp spec β) (ob' : α → oracle_comp spec' β)

section bind

lemma return_bind_equiv (a : α) : (return a >>= ob) ≃ₚ (ob a) :=
(eval_dist_bind (return a) ob).trans (pmf.pure_bind a (λ a, ⦃ob a⦄))

lemma bind_return_equiv : (oa >>= return) ≃ₚ oa :=
trans (eval_dist_bind oa return) (pmf.bind_pure (⦃oa⦄))

lemma bind_equiv_of_equiv_first {oa oa' : oracle_comp spec α} (ob : α → oracle_comp spec β)
  (h : oa ≃ₚ oa') : (oa >>= ob) ≃ₚ (oa' >>= ob) :=
by simp_rw [eval_dist_bind, h]

lemma bind_equiv_of_equiv_second (oa : oracle_comp spec α) {ob ob' : α → oracle_comp spec β}
  (h : ∀ a, (ob a) ≃ₚ (ob' a)) : (oa >>= ob) ≃ₚ (oa >>= ob') :=
by simp_rw [eval_dist_bind, h]

lemma bind_equiv_of_equiv_of_equiv {oa oa' : oracle_comp spec α} {ob ob' : α → oracle_comp spec β}
  (h : oa ≃ₚ oa') (h' :∀ a, (ob a) ≃ₚ (ob' a)) : (oa >>= ob) ≃ₚ (oa' >>= ob') :=
calc oa >>= ob ≃ₚ oa' >>= ob : bind_equiv_of_equiv_first ob h
  ... ≃ₚ oa' >>= ob' : bind_equiv_of_equiv_second oa' h'

lemma bind_const_equiv (oa : oracle_comp spec α) (ob : oracle_comp spec β) :
  oa >>= (λ _, ob) ≃ₚ ob :=
(eval_dist_bind oa _).trans (pmf.bind_const ⦃oa⦄ ⦃ob⦄)

lemma bind_bind_const_equiv (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (oc : α → oracle_comp spec γ) :
  (oa >>= λ a, (ob a >>= λ b, oc a)) ≃ₚ oa >>= oc :=
bind_equiv_of_equiv_second oa (λ a, bind_const_equiv (ob a) _)

end bind

section map

variables (f : α → β)

@[simp]
lemma map_return_equiv (a : α) : f <$> (return a : oracle_comp spec α) ≃ₚ
  (return (f a) : oracle_comp spec β) :=
trans (eval_dist_map (return a) f) (pmf.pure_map f a)

@[simp]
lemma bind_map_equiv (ob : β → oracle_comp spec γ) : (f <$> oa) >>= ob ≃ₚ oa >>= (ob ∘ f) :=
begin
  simp only [eval_dist_bind, eval_dist_map, function.comp_app],
  refine ⦃oa⦄.bind_map f (λ b, ⦃ob b⦄)
end

@[simp]
lemma map_bind_equiv (f : β → γ) : f <$> (oa >>= ob) ≃ₚ oa >>= λ a, f <$> (ob a) :=
begin
  simp only [eval_dist_bind, functor.map, oracle_comp.bind'_eq_bind,
    function.comp_app, eval_dist_return],
  exact ⦃oa⦄.map_bind (λ b, ⦃ob b⦄) f,
end

@[simp]
lemma map_id_equiv : id <$> oa ≃ₚ oa :=
(eval_dist_bind oa _).trans (pmf.bind_pure ⦃oa⦄)

lemma map_equiv_of_equiv {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') : f <$> oa ≃ₚ f <$> oa' :=
by rw [eval_dist_map, eval_dist_map, h]

@[simp]
lemma map_map_equiv (oa : oracle_comp spec α) (f : α → β) (g : β → γ) :
  g <$> (f <$> oa) ≃ₚ (g ∘ f) <$> oa :=
calc ⦃g <$> (f <$> oa)⦄
  = pmf.map g (pmf.map f ⦃oa⦄) : by simp_rw [eval_dist_map]
  ... = pmf.map (g ∘ f) ⦃oa⦄ : pmf.map_comp f ⦃oa⦄ g
  ... = ⦃(g ∘ f) <$> oa⦄ : symm (eval_dist_map oa $ g ∘ f)

lemma map_map_return_equiv (a : α) (f : α → β) (g : β → γ) :
  g <$> (f <$> (return a : oracle_comp spec α)) ≃ₚ (return (g (f a)) : oracle_comp spec γ) :=
by rw [map_map_equiv, map_return_equiv]

end map

/-- Equivalence should be able to erase most unneeded variables using `simp` lemmas.
  Combined with other equivalences can prove many basic things automatically -/
example (n : ℕ) (oa oa' : oracle_comp coin_spec ℕ):
do{ _ ← oa, x ← return 0, y ← return 1, z ← return 2,
    n ← return (x * y), m ← return (n * z),
    b ← coin, _ ← oa, b' ← coin, _ ← oa',
    v ← return (if b then n else m, if b' then m else n),
    return (if b ∧ b' then 0 else v.1 + v.2) } ≃ₚ (return 0 : oracle_comp spec ℕ) := by simp

section prod

variables (f : α → β) (g : α → γ)

@[simp]
lemma fst_map_bind_mk_equiv :
  (prod.fst <$> (oa >>= λ a, return (f a, g a)) : oracle_comp spec β) ≃ₚ f <$> oa :=
by simp only [functor.map, oracle_comp.bind'_eq_bind, eval_dist_bind,
  eval_dist_return, pmf.bind_bind, pmf.pure_bind]

@[simp]
lemma snd_map_bind_mk_equiv :
  (prod.snd <$> (oa >>= λ a, return (f a, g a)) : oracle_comp spec γ) ≃ₚ g <$> oa :=
by simp only [functor.map, oracle_comp.bind'_eq_bind, eval_dist_bind,
  eval_dist_return, pmf.bind_bind, pmf.pure_bind]

end prod

end distribution_semantics