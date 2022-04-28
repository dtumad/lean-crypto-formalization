import computational_monads.oracle_comp
import computational_monads.distribution_semantics.eval_distribution

import to_mathlib.uniform_of_vector
import to_mathlib.to_mathlib

namespace oracle_comp

open oracle_spec

variables {A : Type}

section uniform_fin

def uniform_fin (n : ℕ) :
  oracle_comp uniform_selecting (fin $ n + 1) := query n ()

notation `$[0..` n `]` := uniform_fin n

variables (n : ℕ)

@[simp]
lemma eval_distribution_uniform_fin :
  eval_distribution $[0..n] = pmf.uniform_of_fintype (fin $ n + 1) := rfl

end uniform_fin

section uniform_select_vector

def uniform_select_vector {n : ℕ} (v : vector A (n + 1)) :
  oracle_comp uniform_selecting A := v.nth <$> $[0..n]

notation `$ᵥ` v := uniform_select_vector v

variables {n : ℕ} (v : vector A (n + 1))

@[simp]
lemma eval_distribution_uniform_select_vector :
  eval_distribution ($ᵥ v) = pmf.uniform_of_vector v :=
sorry

end uniform_select_vector

section uniform_select_list

def uniform_select_list : Π (xs : list A) (h : ¬ xs.empty),
  oracle_comp uniform_selecting A
| [] h := false.elim (h rfl)
| (x :: xs) _ := uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩ 

end uniform_select_list

section uniform_select_finset

noncomputable def uniform_select_finset (bag : finset A) (h : bag.nonempty) :
  oracle_comp uniform_selecting A := 
uniform_select_list (bag.to_list) (finset.to_list_nonempty bag h)

end uniform_select_finset

section uniform_select_fintype

noncomputable def uniform_select_fintype (A : Type) [fintype A] [nonempty A] :
  oracle_comp uniform_selecting A :=
uniform_select_finset ⊤ finset.univ_nonempty

end uniform_select_fintype

end oracle_comp