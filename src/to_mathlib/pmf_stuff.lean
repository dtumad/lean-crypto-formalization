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

-- TODO: generalize to higher universes
@[simp]
lemma pmf.map_bind {A B C : Type} (p : pmf A) (q : A → pmf B) (f : B → C) :
  (p.bind q).map f = p.bind (λ a, (q a).map f) :=
pmf.monad_map_eq_map f (p.bind q) ▸ map_bind _

@[simp]
lemma pmf.bind_map {A B C : Type} (p : pmf A) (f : A → B) (q : B → pmf C) :
  (p.map f).bind q = p.bind (q ∘ f) :=
begin
  rw [pmf.map],
  rw [pmf.bind_bind],
  refine congr_arg _ _,
  refine funext (λ a, _),
  rw pmf.pure_bind,
end

@[simp]
lemma pmf.bind_const {A B : Type} (p : pmf A) (q : pmf B) :
  (p.bind $ λ _, q) = q :=
pmf.ext (λ x, by rw [pmf.bind_apply, nnreal.tsum_mul_right _ (q x), pmf.tsum_coe, one_mul])

lemma pmf.to_measure_apply_ne_top {α : Type*} [measurable_space α] (p : pmf α) (s : set α) :
  p.to_measure s ≠ ⊤ := measure_theory.measure_ne_top p.to_measure s

-- TODO: measurable??
lemma pmf.to_outer_measure_apply_ne_top {α : Type*} (p : pmf α) (s : set α) :
  p.to_outer_measure s ≠ ⊤ :=
begin
  refine λ h, (@pmf.to_measure_apply_ne_top α ⊤ p s) (le_antisymm le_top $
    le_trans (le_of_eq h.symm) (@pmf.to_outer_measure_apply_le_to_measure_apply α ⊤ p s)),
end

lemma pmf.indicator_summable {α : Type*} (p : pmf α) (s : set α)
  : summable (s.indicator p) :=
nnreal.summable_of_le (set.indicator_le_self s p) p.summable_coe

lemma pmf.apply_le_one {α : Type*} (p : pmf α) (a : α) : p a ≤ 1 :=
p.coe_le_one a

lemma pmf.to_measure_apply_eq_iff_to_outer_measure_apply_eq {α : Type*} [measurable_space α]
  (p : pmf α) (x : ℝ≥0∞) (s : set α) (hs : measurable_set s) :
  p.to_measure s = x ↔ p.to_outer_measure s = x :=
by rw [p.to_measure_apply_eq_to_outer_measure_apply s hs]

lemma pmf.to_measure_apply_Union {α : Type*} [measurable_space α] (p : pmf α)
  {f : ℕ → set α} (hf : ∀ n, measurable_set (f n)) (h : pairwise (disjoint on f)) :
  p.to_measure (⋃ n, f n) = ∑' n, p.to_measure (f n) :=
p.to_measure.m_Union hf h

lemma pmf.to_outer_measure_apply_Union {α : Type*} (p : pmf α) {f : ℕ → set α}
  (h : pairwise (disjoint on f)) : p.to_outer_measure (⋃ n, f n) = ∑' n, p.to_outer_measure (f n) :=
measure_theory.outer_measure.Union_eq_of_caratheodory _
  (λ n, pmf.measurable_set_to_outer_measure_caratheodory _ (f n)) h