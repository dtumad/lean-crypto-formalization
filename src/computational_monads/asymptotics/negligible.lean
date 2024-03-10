/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.superpolynomial_decay

/-!
# Negligible Functions

This file defines the standard cryptographic notion of a negligible function.
The definition specializes mathlib's `superpolynomial_decay` definition.
-/

namespace asymptotics

open_locale topology polynomial ennreal
open filter (at_top) (tendsto)

-- variables {α : Type*} [topological_space α] [ordered_comm_semiring α]

/-- `superpolynomial_decay` is a more general definition for more general spaces.
  This definition is meant to provide a cleaner API for cryptography proofs -/
def negligible (f : ℕ → ℝ≥0∞) : Prop :=
superpolynomial_decay at_top coe f

lemma negligible_iff_forall_tendsto (f : ℕ → ℝ≥0∞) : negligible f ↔
  ∀ (n : ℕ), tendsto (λ x, ↑x ^ n * f x) at_top (𝓝 0) := iff.rfl

@[simp] lemma negligible_zero : negligible (0 : ℕ → ℝ≥0∞) :=
superpolynomial_decay_zero _ _

variables {f g : ℕ → ℝ≥0∞}

lemma negligible.add (hf : negligible f) (hg : negligible g) : negligible (f + g) :=
superpolynomial_decay.add hf hg

lemma negligible.mul (hf : negligible f) (hg : negligible g) : negligible (f * g) :=
λ n, by simpa [mul_assoc] using ennreal.tendsto.mul
  (hf n) (or.inr ennreal.zero_ne_top) (hg 0) (or.inr ennreal.zero_ne_top)

lemma negligible.pow (hf : negligible f) (n : ℕ) : negligible (f ^ (n + 1)) :=
begin
  induction n with n hn,
  { simpa only [pow_one] using hf },
  { simpa only [pow_succ] using hf.mul hn }
end

lemma negligible.const_mul (hf : negligible f) (r : ℝ≥0∞) (hr : r ≠ ∞) :
  negligible (λ x, r * f x) :=
λ n, by simpa only [zero_mul, ← mul_assoc, mul_comm r]
  using ennreal.tendsto.const_mul (hf n) (or.inr hr)

#check polynomial.coeff

lemma negligible.poly_eval (hf : negligible f) (p : ℝ≥0∞[X]) :
  p.coeff 0 = 0 → (∀ n, p.coeff n ≠ ∞) → negligible (λ x, p.eval (f x)) :=
begin
  refine polynomial.induction_on' p _ _,
  {
    intros p q hp hq h,
    simp_rw [polynomial.eval_add],
    intro h,
    specialize hp sorry sorry,
    specialize hq sorry sorry,
    exact hp.add hq,
  },
  {
    simp,
    intros n r hp hr,
    specialize hr n,
    simp_rw [polynomial.coeff_monomial] at hp,
    simp_rw [polynomial.coeff_monomial, eq_self_iff_true, if_true] at hr,
    have := (hf.pow n.pred).const_mul r hr,
    sorry,
  }
end

end asymptotics
