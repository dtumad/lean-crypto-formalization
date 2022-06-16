import measure_theory.probability_mass_function.basic
import data.vector.basic

open_locale nnreal ennreal

lemma pmf.apply_eq_one_iff {A : Type} (p : pmf A) (a : A) :
  p a = 1 ↔ p.support = {a} :=
sorry

lemma vector.not_mem_to_list_of_length_zero {A : Type} (v : vector A 0) (a : A) :
  a ∉ v.to_list :=
begin
  rw [vector.eq_nil v],
  exact id,
end