/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.generate
import computational_monads.query_tracking.query_seed.basic

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

open_locale big_operators
open oracle_spec oracle_spec.indexed_list

variables {α β γ : Type} {spec : oracle_spec}

/-- Given a count of queries `qc`, and an initial `query_store` seed, generate more outputs at
random until the number of seeded outputs for each oracle is at least the value given in `qc`. -/
noncomputable def generate_seed (qc : spec.query_count) :
  oracle_comp uniform_selecting (spec.query_seed) :=
generate qc (λ i, $ᵗ (spec.range i))

variables (qc : spec.query_count)

@[simp] lemma support_generate_seed : (generate_seed qc).support = {qs | ↑qs = qc} :=
by simp only [generate_seed, support_generate, mem_support_uniform_select_fintype,
  list.all₂_iff_forall, imp_true_iff, and_true]

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

end oracle_comp