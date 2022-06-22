import computational_monads.oracle_comp
import computational_monads.distribution_semantics.eval_distribution

import measure_theory.probability_mass_function.monad 
import to_mathlib.uniform_of_vector
import to_mathlib.general

namespace oracle_comp

open oracle_spec
open_locale classical

variables {A : Type}

section uniform_fin

/-- Randomly choose a natural `n : ℕ` by querying the uniform selection oracle.
  We implicitly use a `succ` call for the resulting type since `fin 0` is unihabited as a type -/
def uniform_fin (n : ℕ) :
  oracle_comp uniform_selecting (fin $ n + 1) :=
query n ()

notation `$[0..` n `]` := uniform_fin n

variables (n : ℕ)

@[simp]
lemma support_uniform_fin :
  support $[0..n] = ⊤ :=
support_query n ()

@[simp]
lemma eval_distribution_uniform_fin :
  ⟦$[0..n]⟧ = pmf.uniform_of_fintype (fin $ n + 1) :=
rfl

@[simp]
lemma eval_distribution_uniform_fin_apply (m : fin $ n + 1) :
  ⟦$[0..n]⟧ m = 1 / (n + 1) :=
by simp only [eval_distribution_uniform_fin n, pmf.uniform_of_fintype_apply m,
  fintype.card_fin (n + 1), nat.cast_add, nat.cast_one, one_div]

@[simp]
lemma prob_event_uniform_fin (event : set (fin $ n + 1)) :
  ⟦event | $[0..n]⟧ = (fintype.card event) / (n + 1) :=
by simp only [uniform_fin, eval_prob_query, uniform_selecting.range_apply,
  fintype.card_fin, nat.cast_add, nat.cast_one]

end uniform_fin

section uniform_select_vector

/-- Randomly select an element of a vector by using `uniform_of_fin`.
  Again we need to use `succ` for the vectors type to avoid sampling an empty vector -/
def uniform_select_vector {n : ℕ} (v : vector A (n + 1)) :
  oracle_comp uniform_selecting A := v.nth <$> $[0..n]

notation `$ᵛ` v := uniform_select_vector v

variables {n : ℕ} (v : vector A (n + 1))

@[simp]
lemma support_uniform_of_vector :
  support ($ᵛ v) = v.nth '' ⊤ :=
begin
  rw uniform_select_vector,
  rw support_map,
  rw support_uniform_fin,
end

@[simp]
lemma eval_distribution_uniform_select_vector :
  ⟦$ᵛ v⟧ = pmf.uniform_of_vector v :=
begin
  sorry
end

end uniform_select_vector

section uniform_select_list

/-- If a list isn't empty, we can convert it to a vector and then sample from it.
  TODO: this should probably correspond to an actual `pmf` function -/
def uniform_select_list : Π (xs : list A) (h : ¬ xs.empty),
  oracle_comp uniform_selecting A
| [] h := false.elim (h rfl)
| (x :: xs) _ := uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩ 

notation `$ˡ` := uniform_select_list

variables (xs : list A) (h : ¬ xs.empty)

@[simp]
lemma support_uniform_select_list :
  support ($ˡ xs h) = {a | a ∈ xs} :=
sorry

end uniform_select_list

section uniform_select_finset

/-- We can sample randomly from a `finset` by converting to a list and then sampling that.
  Note this conversion is noncomputable, this conversion uses the axiom of choice. -/
noncomputable def uniform_select_finset (bag : finset A) (h : bag.nonempty) :
  oracle_comp uniform_selecting A := 
uniform_select_list (bag.to_list) (finset.to_list_nonempty bag h)

notation `$ˢ` := uniform_select_finset

variables (bag : finset A) (h : bag.nonempty)

@[simp]
lemma support_uniform_select_finset :
  support ($ˢ bag h) = ↑bag :=
sorry

@[simp]
lemma eval_distribution_uniform_select_finset :
  ⟦$ˢ bag h⟧ = pmf.uniform_of_finset bag h :=
sorry

end uniform_select_finset

section uniform_select_fintype

/-- We can select randomly from a fintyp by using the `finset` corresponding to the `fintype`.
  Again we need to use axiom of choice so this operation is noncomputable. -/
noncomputable def uniform_select_fintype (A : Type) [fintype A] [nonempty A] :
  oracle_comp uniform_selecting A :=
uniform_select_finset ⊤ finset.univ_nonempty

notation `$ᵗ` := uniform_select_fintype

variables (A) [fintype A] [nonempty A]

@[simp]
lemma support_uniform_select_fintype :
  support ($ᵗ A) = ⊤ :=
sorry

@[simp]
lemma eval_distribution_uniform_select_fintype :
  ⟦$ᵗ A⟧ = pmf.uniform_of_fintype A :=
sorry

end uniform_select_fintype

end oracle_comp