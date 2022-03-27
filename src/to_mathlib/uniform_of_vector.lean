import measure_theory.probability_mass_function.constructions

noncomputable theory

variables {α : Type} --[decidable_eq α]

open_locale classical big_operators nnreal ennreal

lemma vector.to_list_nonempty {n : ℕ} (v : vector α (n + 1)) : ¬ v.to_list.empty :=
match v with | ⟨a :: as, _⟩ := by simp end

def pmf.uniform_of_vector {n : ℕ} (v : vector α (n + 1)) : pmf α :=
pmf.of_multiset (quotient.mk v.to_list)
(by simpa only [multiset.quot_mk_to_coe, ne.def, multiset.coe_eq_zero, ← list.empty_iff_eq_nil]
  using vector.to_list_nonempty v)