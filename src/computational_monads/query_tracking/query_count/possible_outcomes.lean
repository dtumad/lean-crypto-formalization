/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.order
import algebra.big_operators.ring

/-!
# Possible Ways to Choose Query Outputs

This file defines a function `possible_outcomes` that takes a `query_count` and returns
the number of ways to choose query outputs for all of the queries.

In particular this will give the probability of getting an output from `generate_seed`.
-/

namespace oracle_comp

open_locale big_operators
open oracle_spec query_count

variables {α β γ : Type} {spec : oracle_spec}

/-- Given a count of a number of queries to each oracle, get the number of possible outcomes,
assuming that each of the oracles could respond with any output. -/
def possible_outcomes (qc : query_count spec) : ℕ :=
∏ i in qc.active_oracles, (fintype.card (spec.range i)) ^ (qc i)

variables (qc qc' : query_count spec)

@[simp] lemma possible_outcomes_ne_zero : possible_outcomes qc ≠ 0 :=
finset.prod_ne_zero_iff.2 (λ i hi, pow_ne_zero _ (card_range_ne_zero i))

@[simp] lemma possible_outcomes_pos : 0 < possible_outcomes qc :=
pos_iff_ne_zero.2 (possible_outcomes_ne_zero qc)

@[simp] lemma possible_outcomes_empty : possible_outcomes (∅ : query_count spec) = 1 := rfl

@[simp] lemma possible_outcomes_of_nat (i : spec.ι) (n) : possible_outcomes (of_nat i n) =
  (fintype.card (spec.range i)) ^ n :=
begin
  simp [possible_outcomes],
  exact λ hn, hn.symm ▸ (pow_zero _).symm,
end

@[simp] lemma possible_outcomes_add : possible_outcomes (qc + qc') =
  possible_outcomes qc * possible_outcomes qc' :=
begin
  simp [possible_outcomes, pow_add, finset.prod_mul_distrib],
  congr' 1,
  { rw [← finset.union_sdiff_self_eq_union, finset.prod_union finset.disjoint_sdiff],
    refine trans (congr_arg _ (finset.prod_eq_one (λ i hi, _))) (mul_one _),
    rw [apply_eq_zero _ (finset.mem_sdiff.1 hi).2, pow_zero] },
  { rw [← finset.sdiff_union_self_eq_union, finset.prod_union finset.sdiff_disjoint, mul_comm],
    refine trans (congr_arg _ (finset.prod_eq_one (λ i hi, _))) (mul_one _),
    rw [apply_eq_zero _ (finset.mem_sdiff.1 hi).2, pow_zero] }
end

@[simp] lemma possible_outcomes_increment (i n) : possible_outcomes (qc.increment i n) =
  (possible_outcomes qc) * (fintype.card (spec.range i)) ^ n :=
by rw [← add_of_nat, possible_outcomes_add, possible_outcomes_of_nat]

lemma possible_outcomes_dvd_possible_outcomes (h : qc' ≤ qc) :
  (possible_outcomes qc') ∣ (possible_outcomes qc) :=
begin
  obtain ⟨qc₀, rfl⟩ := exists_add_of_le h,
  simp only [possible_outcomes_add, dvd_mul_right],
end

lemma possible_outcomes_sub (h : qc' ≤ qc) : possible_outcomes (qc - qc') =
  possible_outcomes qc / possible_outcomes qc' :=
begin
  rw [eq_comm, nat.div_eq_iff_eq_mul_left (possible_outcomes_pos _),
    ← possible_outcomes_add, tsub_add_cancel_of_le h],
  exact possible_outcomes_dvd_possible_outcomes qc qc' h
end

@[simp] lemma possible_outcomes_decrement {i n} (h : n ≤ qc i) :
  possible_outcomes (qc.decrement i n) =
    (possible_outcomes qc) / (fintype.card (spec.range i)) ^ n :=
by rw [← sub_of_nat, possible_outcomes_sub _ _ ((of_nat_le_iff _ _ _).2 h),
  possible_outcomes_of_nat]

end oracle_comp