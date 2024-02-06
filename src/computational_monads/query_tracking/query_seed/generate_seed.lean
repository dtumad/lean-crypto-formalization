/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.generate
import computational_monads.query_tracking.indexed_list.get_or_else
import computational_monads.query_tracking.query_seed.basic
import computational_monads.coercions.instances

/-!
# Pre-Computation of Queries Made by a Computation

This file defines a function `generate_seed` that pre-computes a number of oracle outputs that can
be used in a computation, choosing them all uniformly at random.
The output is given by a `query_seed`, and the count is specified by a `query_count`.

If the number of seeded values is higher than the specified count the values remain unchanged.
The order in which the values are generated isn't specifically defined, as we use `finset.to_list`
to determine the ordering, and so the definition is noncomputable.
-/

namespace oracle_comp

open_locale big_operators ennreal
open oracle_spec oracle_spec.indexed_list oracle_spec.query_count

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Given a count of queries `qc`, and an initial `query_store` seed, generate more outputs at
random until the number of seeded outputs for each oracle is at least the value given in `qc`. -/
noncomputable def generate_seed (qc : spec.query_count) :
  oracle_comp unif_spec spec.query_seed :=
generate qc (λ i, $ᵗ (spec.range i))

variables (qc qc' : spec.query_count)

@[simp] lemma support_generate_seed : (generate_seed qc).support = {qs | ↑qs = qc} :=
by simp only [generate_seed, support_generate, mem_support_uniform_select_fintype,
  list.all₂_iff_forall, imp_true_iff, and_true]

lemma coe_of_mem_support_generate_seed {qs : spec.query_seed}
  {qc : spec.query_count} (h : qs ∈ (generate_seed qc).support) : ↑qs = qc :=
by simpa using h

lemma coe_of_mem_fin_support_generate_seed {qs : spec.query_seed}
  {qc : spec.query_count} (h : qs ∈ (generate_seed qc).fin_support) : ↑qs = qc := 
by simpa [mem_fin_support_iff_mem_support] using h

@[simp] lemma prob_output_generate_seed (qs : spec.query_seed) (h : ↑qs = qc) :
  ⁅= qs | generate_seed qc⁆ = (possible_outcomes qc)⁻¹ :=
begin
  refine trans (prob_output_generate qc _ qs h) (ennreal.eq_inv_of_mul_eq_one_left _),
  simp only [possible_outcomes, nat.cast_prod, ← h, coe_query_count_eq,
    active_oracles_to_query_count, ← finset.prod_mul_distrib],
  refine finset.prod_eq_one (λ j hj, _),
  have : ⇑⁅$ᵗ (spec.range j)⁆ = λ _, (↑(fintype.card (spec.range j)))⁻¹,
  from funext (λ i, prob_output_uniform_select_fintype _ i),
  rw [this, list.map_const, list.prod_replicate, ← get_count_eq_length_apply,
    nat.cast_pow, ← ennreal.inv_pow, get_count_to_query_count],
  exact ennreal.inv_mul_cancel (ennreal.pow_ne_zero (nat.cast_ne_zero.2 fintype.card_ne_zero) _)
    (ennreal.pow_ne_top (ennreal.nat_ne_top _))
end

@[simp] lemma card_fin_support_generate_seed :
  (generate_seed qc).fin_support.card = possible_outcomes qc :=
begin
  have : (↑(generate_seed qc).fin_support.card : ℝ≥0∞) * (possible_outcomes qc)⁻¹ = 1,
  { rw [finset.card_eq_sum_ones, nat.cast_sum, finset.sum_mul, nat.cast_one, one_mul],
    refine trans _ (generate_seed qc).sum_prob_output,
    refine finset.sum_congr rfl (λ qs hqs, symm (prob_output_generate_seed qc qs _)),
    refine coe_of_mem_fin_support_generate_seed hqs },
  refine (@nat.cast_inj ℝ≥0∞ _ _ _ _).1 (trans _ (one_mul _)),
  rw [← this, mul_assoc, ennreal.inv_mul_cancel, mul_one]; simp,
end

lemma generate_seed_of_nat (i : spec.ι) (n : ℕ) :
  generate_seed (of_nat i n) = of_list <$> (repeat ($ᵗ (spec.range i)) n) :=
by rw [generate_seed, generate_of_nat]

@[pairwise_dist_equiv] lemma generate_seed_add_dist_equiv :
  generate_seed (qc + qc') ≃ₚ (+) <$> generate_seed qc <*> generate_seed qc' :=
generate_add_dist_equiv qc qc' _

lemma generate_seed_add_dist_equiv' (qc' : spec.query_count → spec.query_count) :
  generate_seed (qc + qc' qc) ≃ₚ
    do {qs ← generate_seed qc, qs' ← generate_seed (qc' ↑qs), return (qs + qs')} :=
begin
  rw_dist_equiv [generate_seed_add_dist_equiv],
  rw [seq_map_eq_bind_bind],
  pairwise_dist_equiv 1 with qs hqs,
  rw [coe_of_mem_support_generate_seed hqs],
end

lemma generate_seed_dist_equiv_add_sub (h : qc' ≤ qc) :
  generate_seed qc ≃ₚ (+) <$> generate_seed qc' <*> generate_seed (qc - qc') :=
begin
  refine trans _ (generate_seed_add_dist_equiv qc' (qc - qc')),
  rwa [add_tsub_cancel_of_le],
end

section get_head

lemma map_get_head_generate_seed (qc : spec.query_count) (i : spec.ι) (h : i ∈ qc.active_oracles) :
  (λ seed, indexed_list.get_head seed i) <$> generate_seed qc ≃ₚ
    prod.mk <$> ($ᵗ (spec.range i)) <*> generate_seed (qc.decrement i 1) :=
begin
  have := generate_seed_dist_equiv_add_sub qc (of_nat i 1) (by simpa using h),
  refine trans (map_dist_equiv_of_dist_equiv' rfl this) _,
  rw [map_seq],
  simp [function.comp, generate_seed_of_nat, ← decrement_eq_sub_of_nat,
    seq_eq_bind_map, oracle_comp.map_eq_bind_return_comp, bind_assoc],
  pairwise_dist_equiv 2 with i hi qs hqs,
  simp,
end

lemma map_nth_generate_seed_dist_equiv (qc : spec.query_count) (i : spec.ι) (n : ℕ) :
  (λ seed : spec.query_seed, (seed i).nth n) <$> generate_seed qc ≃ₚ
    if n < qc.get_count i then some <$> ($ᵗ (spec.range i)) else return none :=
begin
  sorry,
end

-- lemma map_get_head_generate_seed_dist_equiv [h : is_sub_spec unif_spec spec]
--   (i : spec.ι) (hi : i ∈ qc.active_oracles) :
--   (λ qc, indexed_list.get_head qc i) <$> generate_seed qc ≃ₚ
--     ($ᵗ (spec.range i) ×ₘ generate_seed (qc.decrement i 1)) :=
-- begin
--   sorry,
--   -- rw_dist_equiv [generate_seed_dist_equiv_of_mem_active_oracles _ _ hi],
--   -- simp [oracle_comp.bind_return_comp_eq_map],
--   -- -- rw_dist_equiv [map_bind_dist_equiv, map_comp_dist_equiv],
--   -- rw [mprod],
--   -- simp_rw [oracle_comp.bind_return_comp_eq_map],
--   -- pairwise_dist_equiv,
--   -- simp,
-- end

-- lemma map_fst_get_head_generate_seed_dist_equiv [h : is_sub_spec unif_spec spec]
--   (i : spec.ι) (hi : i ∈ qc.active_oracles) :
--   (λ qc, (indexed_list.get_head qc i).1) <$> generate_seed qc ≃ₚ $ᵗ (spec.range i) :=
-- begin
--   refine trans (map_comp_dist_equiv (generate_seed qc)
--     (λ qc, indexed_list.get_head qc i) prod.fst).symm _,
--   rw_dist_equiv [map_get_head_generate_seed_dist_equiv _ _ hi, fst_map_mprod_dist_equiv],
-- end

end get_head

end oracle_comp