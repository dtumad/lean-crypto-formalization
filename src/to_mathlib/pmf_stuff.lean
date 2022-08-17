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
