import Comp
import measure_theory.probability_mass_function
import data.real.nnreal

import algebra.big_operators.basic

open_locale big_operators nnreal

variables {A B : Type}

namespace Comp

lemma sum_bitvec_eq_one {n : ℕ} : has_sum (λ (v : bitvec n), ((2 : nnreal) ^ n)⁻¹) 1 :=
begin
  convert has_sum_fintype (λ (v : bitvec n), ((2 : nnreal) ^ n)⁻¹),
  rw [finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv],
  have : (finset.univ : finset (bitvec n)).card = 2 ^ n :=
    (by rw [card_vector n, fintype.card_bool] : fintype.card (bitvec n) = 2 ^ n),
  simp [this, div_self (λ h, two_ne_zero (pow_eq_zero h) : (2 : nnreal) ^ n ≠ 0)],
end

lemma tsum_ne_zero_iff {α : Type*} (f : α → ℝ≥0) (hf : summable f) :
  tsum f ≠ 0 ↔ ∃ (a : α), f a ≠ 0 :=
by rwa [ne.def, tsum_eq_zero_iff hf, not_forall]

section eval_distribution

private noncomputable def eval_distribution' (ca : Comp A) (h : ca.support.nonempty) : 
  Σ (da : pmf A), plift (∀ (a : A), (da a ≠ 0 ↔ a ∈ ca.support)) :=
begin
  refine ca.rec_on _ _ _ _,
  { 
    refine λ _ _ a, ⟨pmf.pure a, plift.up (by simp)⟩,
  },
  { 
    refine λ A B ca cb db da, ⟨db.1.bind (λ b, (da b).1), plift.up (λ a, _)⟩,
    rw [mem_support_bind_iff, pmf.bind_apply, 
      tsum_ne_zero_iff _ (pmf.bind.summable db.1 (λ b, (da b).1) a)],
    split; rintro ⟨b, hb⟩;  
      cases (da b).2 with hda; specialize hda a; 
      cases db.2 with hdb; refine ⟨b, _⟩,
    { simp [not_or_distrib] at hb,
      rwa [← hdb b, ← hda] },
    { simp [not_or_distrib],
      rwa [← hdb b, ← hda] at hb }
  },
  { 
    refine λ n, ⟨⟨λ v, ((2 : nnreal) ^ n)⁻¹, sum_bitvec_eq_one⟩, plift.up (λ v, _)⟩,
    simp only [support_rnd, finset.mem_univ, iff_true, ne.def],
    refine λ hn, two_ne_zero (pow_eq_zero (inv_eq_zero.mp hn) : (2 : nnreal) = 0),
  },
  {
    intros A p hp ca da,
    sorry,
  }
end

/-- The denotational semantics of a `Comp A` is the distribution of resulting values.
  This distribution is given in the form of a `pmf` on the type `A` of the computation.
  Defined for any computation with nonempty support, but only meaningful if `ca` is well formed -/
noncomputable def eval_distribution (ca : Comp A) (hca : ca.support.nonempty) : pmf A :=
(eval_distribution' ca hca).fst

theorem eval_distribution_ne_zero_iff (ca : Comp A) (hca : ca.support.nonempty) (a : A) :
  (eval_distribution ca hca a) ≠ 0 ↔ a ∈ ca.support :=
plift.rec (λ h, h a) (eval_distribution' ca hca).snd

@[simp] lemma eval_distribution_ret [decidable_eq A] (a : A) (h : (ret a).support.nonempty) :
  eval_distribution (ret a) h = pmf.pure a := rfl

@[simp] lemma eval_distribution_bind (cb : Comp B) (ca : B → Comp A) 
  (h : (bind cb ca).support.nonempty) 
  (hb : cb.support.nonempty) (ha : ∀ b, (ca b).support.nonempty):
  eval_distribution (bind cb ca) h = (eval_distribution cb hb).bind 
    (λ b, (eval_distribution (ca b) (ha b))) := rfl

@[simp] lemma eval_distribution_rnd {n : ℕ} (h : (rnd n).support.nonempty) :
  eval_distribution (rnd n) h = ⟨λ v, ((2 : nnreal) ^ n)⁻¹, sum_bitvec_eq_one⟩ := rfl

end eval_distribution

end Comp