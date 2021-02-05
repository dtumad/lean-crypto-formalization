import Comp
import measure_theory.probability_mass_function
import data.real.nnreal

import algebra.big_operators.basic

open_locale big_operators

variables {A : Type}

namespace Comp

lemma sum_bitvec_eq_one {n : ℕ} : has_sum (λ (v : bitvec n), ((2 : nnreal) ^ n)⁻¹) 1 :=
begin
  convert has_sum_fintype (λ (v : bitvec n), ((2 : nnreal) ^ n)⁻¹),
  rw [finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv],
  have : (finset.univ : finset (bitvec n)).card = 2 ^ n :=
    (by rw [card_vector n, fintype.card_bool] : fintype.card (bitvec n) = 2 ^ n),
  simp [this, div_self (λ h, two_ne_zero (pow_eq_zero h) : (2 : nnreal) ^ n ≠ 0)],
end

/-- The denotational semantics of a `Comp A` is the distribution of resulting values.
  This distribution is given in the form of a `pmf` on the type `A` of the computation -/
noncomputable def eval_distribution (ca : Comp A) : pmf A :=
begin
  refine ca.rec_on _ _ _ _,
  { exact λ _ _ a, pmf.pure a },
  { exact λ _ _ _ _ db da, db.bind da },
  { exact λ n, ⟨λ v, (2 ^ n)⁻¹, sum_bitvec_eq_one⟩ },
  {
    intros A ca p da,
    sorry,
  }
end


end Comp