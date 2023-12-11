/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import computational_monads.distribution_semantics.tactics.rw_dist_equiv

open_locale nnreal

section naive_prob_comp

inductive naive_prob_comp : Type → Type 1
| pure' (A : Type) (a : A) : naive_prob_comp A
| bind' (A B : Type) (pa : naive_prob_comp A)
    (pb : A → naive_prob_comp B) :
    naive_prob_comp B
| coin : naive_prob_comp bool

end naive_prob_comp

section prob_comp'

def prob_comp' : Type → Type :=
λ A, {f : A → ℝ≥0 // tsum f = 1}

def prob_comp'.pure (A : Type)
  [decidable_eq A] (a : A) : prob_comp' A :=
⟨λ a', if a = a' then 1 else 0, sorry⟩

noncomputable def prob_comp'.bind (A B : Type) (pa : prob_comp' A)
  (pb : A → prob_comp' B) : prob_comp' B :=
⟨λ b, ∑' a : A, pa.1 a * (pb a).1 b, sorry⟩

noncomputable def prob_comp'.coin : prob_comp' bool :=
⟨λ _, 1 / 2, sorry⟩

end prob_comp'

section prob_comp

inductive prob_comp : Type → Type 1
| pure' (A : Type) (a : A) : prob_comp A
| coin_bind' (A : Type) (pa : bool → prob_comp A) :
    prob_comp A

open prob_comp

def prob_comp.bind : Π (A B : Type), prob_comp A →
  (A → prob_comp B) → prob_comp B
| A B (pure' _ a) pb := pb a
| A B (coin_bind' _ pa) pb :=
    coin_bind' B (λ b, prob_comp.bind A B (pa b) pb)

@[inline, reducible]
def prob_comp_real (A : Type) : Type 1 :=
oracle_comp oracle_spec.coin_spec A

end prob_comp

section main

open oracle_comp oracle_spec

example : oracle_comp coin_spec bool :=
do { b1 ← coin, b2 ← coin,
  return (bxor b1 b2) }

end main
