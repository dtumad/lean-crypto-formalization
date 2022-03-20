import computational_monads.probabalistic_computation.oracle_comp

open oracle_comp oracle_comp_spec

variables {A : Type}

def uniform_fin (n : ℕ) :
  oracle_comp uniform_selecting (fin $ n + 1) := query n ()

notation `$[0..` n `]` := uniform_fin n

def uniform_select_vector {n : ℕ} (v : vector A (n + 1)) :
  oracle_comp uniform_selecting A := v.nth <$> $[0..n] 

def uniform_select_list : Π (xs : list A) (h : ¬ xs.empty),
  oracle_comp uniform_selecting A
| [] h := false.elim (h rfl)
| (x :: xs) _ := uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩ 

noncomputable def uniform_select_finset (bag : finset A) (h : bag.nonempty) :
  oracle_comp uniform_selecting A := 
uniform_select_list (bag.to_list) (let ⟨x, hx⟩ := h in
  λ h', list.not_mem_nil x ((list.empty_iff_eq_nil.1 h') ▸ (finset.mem_to_list bag).2 hx))

noncomputable def uniform_select_fintype {A : Type} [fintype A] [nonempty A] :
  oracle_comp uniform_selecting A :=
uniform_select_finset ⊤ finset.univ_nonempty
