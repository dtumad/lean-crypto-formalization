import Comp
import measure_theory.probability_mass_function
import data.real.nnreal

import algebra.big_operators.basic

open_locale big_operators

variables {A : Type}

namespace Comp

lemma sum_bitvec_eq_one {n : ℕ} : has_sum (λ (v : bitvec n), 1 / (2 : nnreal) ^ n) 1 :=
begin
  convert has_sum_fintype (λ (v : bitvec n), 1 / (2 : nnreal) ^ n),
  rw [finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_one],
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
  { exact λ n, ⟨λ v, 1 / (2 ^ n), sum_bitvec_eq_one⟩ },
  {
    intros A ca p da,
    let weight : nnreal := ∑ a in ca.support, if p a = tt then da a else 0,
    refine ⟨λ a, (if p a = tt then da a else 0) * weight⁻¹, _⟩,
    have := @has_sum.mul_right _ _ _ _ _ (λ a, if p a = tt then da a else 0) weight weight⁻¹ _,
    have hweight : weight * weight⁻¹ = 1 := mul_inv_cancel sorry,
    simp at this ⊢,
    exact hweight ▸ this,
    sorry,
    
  }
end


end Comp