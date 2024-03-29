/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.generate
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

@[simp] lemma support_generate_seed : (generate_seed qc).support = {qs | qs.to_query_count = qc} :=
by simp only [generate_seed, support_generate, mem_support_uniform_select_fintype,
  list.all₂_iff_forall, imp_true_iff, and_true]

lemma coe_of_mem_support_generate_seed {qs : spec.query_seed}
  {qc : spec.query_count} (h : qs ∈ (generate_seed qc).support) : ↑qs = qc :=
by simpa using h

lemma to_query_count_of_mem_support_generate_seed {qs : spec.query_seed}
  {qc : spec.query_count} (h : qs ∈ (generate_seed qc).support) : qs.to_query_count = qc :=
by simpa using h

lemma coe_of_mem_fin_support_generate_seed {qs : spec.query_seed}
  {qc : spec.query_count} (h : qs ∈ (generate_seed qc).fin_support) : ↑qs = qc :=
by simpa [mem_fin_support_iff_mem_support] using h

lemma to_query_count_of_mem_fin_support_generate_seed {qs : spec.query_seed}
  {qc : spec.query_count} (h : qs ∈ (generate_seed qc).fin_support) : qs.to_query_count = qc :=
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

-- TODO: shouldn't have need for this lemma
@[simp] lemma prob_output_generate_seed_bind [unif_spec ⊂ₒ spec]
  (oc : spec.query_seed → oracle_comp spec γ) (z : γ) :
  ⁅= z | ↑(generate_seed qc) >>= oc⁆ =
    ∑ qs in (generate_seed qc).fin_support, (possible_outcomes qc)⁻¹ * ⁅= z | oc qs⁆ :=
begin
  rw [prob_output_bind_eq_sum, fin_support_coe_sub_spec],
  refine finset.sum_congr rfl (λ qs hqs, _),
  rw [prob_output_coe_sub_spec, prob_output_generate_seed _ _
    (coe_of_mem_fin_support_generate_seed hqs)],
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

@[simp] lemma generate_seed_of_nat (i : spec.ι) (n : ℕ) :
  generate_seed (of_nat i n) = of_list <$> (repeat ($ᵗ (spec.range i)) n) :=
by rw [generate_seed, generate_of_nat]

@[pairwise_dist_equiv] lemma generate_seed_add_dist_equiv :
  generate_seed (qc + qc') ≃ₚ (+) <$> generate_seed qc <*> generate_seed qc' :=
generate_add_dist_equiv qc qc' _

/-- Dependent version of `generate_seed_add_dist_equiv`. -/
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
generate_dist_equiv_add_sub qc qc' _ h

lemma map_pop_generate_seed (qc : spec.query_count) (i : spec.ι) (h : i ∈ qc.active_oracles) :
  (λ seed, indexed_list.pop seed i) <$> generate_seed qc ≃ₚ
    prod.mk <$> ($ᵗ (spec.range i)) <*> generate_seed (qc.decrement i 1) :=
map_pop_generate qc _ _ h

lemma map_nth_generate_seed_dist_equiv (qc : spec.query_count) (i : spec.ι) (n : ℕ) :
  (λ seed : spec.query_seed, (seed i).nth n) <$> generate_seed qc ≃ₚ
    if n < qc.get_count i then some <$> $ᵗ (spec.range i) else return none :=
map_nth_generate qc _ i n

end oracle_comp