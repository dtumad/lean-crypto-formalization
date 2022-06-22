import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials 

/-!
# Miscelanious Lemams

This file is a collection of random statements that maybe should eventually move to mathlib.
Most of these are things that could usually be "handwaved" away in proofs. 
-/


lemma finset.to_list_nonempty {A : Type} (s : finset A) (hs : s.nonempty) : ¬ s.to_list.empty :=
let ⟨x, hx⟩ := hs in
  λ h', list.not_mem_nil x ((list.empty_iff_eq_nil.1 h') ▸ (finset.mem_to_list s).2 hx)

section asymptotics

open asymptotics


end asymptotics