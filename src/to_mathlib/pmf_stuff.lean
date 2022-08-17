import to_mathlib.general

import probability.probability_mass_function.uniform

/-!
# Lemmas about probability mass functions to move to mathlib 
-/

open_locale measure_theory nnreal ennreal classical big_operators

variables {α β γ : Type*}

lemma pmf.measurable_set_to_outer_measure_caratheodory (p : pmf α) (s : set α) :
  measurable_set[p.to_outer_measure.caratheodory] s :=
p.to_outer_measure_caratheodory.symm ▸ measurable_space.measurable_set_top

lemma pmf.map_bind {A B C : Type} (p : pmf A) (q : A → pmf B) (f : B → C) :
  (p >>= q).map f = p >>= (λ a, (q a).map f) :=
pmf.monad_map_eq_map f (p >>= q) ▸ map_bind _

lemma pmf.bind_map {A B C : Type} (p : pmf A) (f : A → B) (q : B → pmf C) :
  (p.map f) >>= q = p >>= (q ∘ f) :=
begin
  ext x,
  sorry
end

-- TODO: change pure-map `->` map_pure

@[simp]
lemma pmf.bind_const {A B : Type} (p : pmf A) (q : pmf B) :
  (p.bind $ λ _, q) = q :=
pmf.ext (λ x, by rw [pmf.bind_apply, nnreal.tsum_mul_right _ (q x), pmf.tsum_coe, one_mul])

lemma pmf.bind_const' {A B : Type} (p : pmf A) (q : pmf B) :
  (p >>= λ _, q) = q :=
pmf.bind_const p q