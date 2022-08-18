import to_mathlib.general

import probability.probability_mass_function.uniform

/-!
# Lemmas about probability mass functions to move to mathlib 
-/

open_locale measure_theory nnreal ennreal big_operators

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

lemma pmf.to_measure_apply_ne_top {α : Type*} [measurable_space α] (p : pmf α) (s : set α) :
  p.to_measure s ≠ ⊤ := measure_theory.measure_ne_top p.to_measure s

lemma pmf.to_outer_measure_apply_ne_top {α : Type*} [measurable_space α] (p : pmf α) (s : set α) :
  p.to_outer_measure s ≠ ⊤ :=
begin
  refine λ h, (p.to_measure_apply_ne_top s) (le_antisymm le_top $
    le_trans (le_of_eq h.symm) (pmf.to_outer_measure_apply_le_to_measure_apply p s)),
end

#check nnreal.indicator_summable

lemma ennreal.indicator_summable (α : Type*) (f : α → ℝ≥0∞) (hf : summable f) (s : set α) :
  summable (s.indicator f) :=
begin
  refine ennreal.summable, 
end

lemma pmf.indicator_summable {α : Type*} [measurable_space α] (p : pmf α) (s : set α)
  : summable (s.indicator p) :=
begin
  sorry
end

lemma pmf.apply_le_one {α : Type*} (p : pmf α) (a : α) : p a ≤ 1 :=
begin
  sorry
end
