/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.constructions.uniform_select

/-!
# Probabilities for Computations Over Option Type

General lemmas about probability computations involving `option`.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

@[simp] lemma prob_output_bnot_map (oa : oracle_comp spec bool) (b : bool) :
  ⁅= b | bnot <$> oa⁆ = ⁅= bnot b | oa⁆ :=
begin
  refine prob_output_map_eq_single _ _ _ _ (set.ext (λ b', _)),
  cases b; simp only [set.mem_preimage, set.mem_singleton_iff, bnot_eq_ff_eq_eq_tt,
    bool.bnot_ff, bnot_eq_true_eq_eq_ff, bool.bnot_tt]
end

section uniform_select_bool

lemma prob_output_uniform_select_bool (x : bool) :
  ⁅= x | $ᵗ bool⁆ = 1 / 2 := by simp

lemma prob_output_uniform_select_bool_bind
  (oa : bool → oracle_comp uniform_selecting α) (x : α) :
  ⁅= x | $ᵗ bool >>= oa⁆ = (⁅= x | oa tt⁆ + ⁅= x | oa ff⁆) / 2 :=
by simp only [prob_output_uniform_select_fintype_bind_apply_eq_sum, fintype.univ_bool,
  finset.sum_insert, finset.mem_singleton, not_false_iff, finset.sum_singleton,
  fintype.card_bool, nat.cast_bit0, algebra_map.coe_one]

lemma prob_event_uniform_select_bool_bind
  (oa : bool → oracle_comp uniform_selecting α) (e : set α) :
  ⁅e | $ᵗ bool >>= oa⁆ = (⁅e | oa tt⁆ + ⁅e | oa ff⁆) / 2 :=
by simp only [prob_event_uniform_select_fintype_bind_eq_sum, fintype.univ_bool,
  finset.sum_insert, finset.mem_singleton, not_false_iff, finset.sum_singleton, fintype.card_bool,
  nat.cast_bit0, algebra_map.coe_one]

end uniform_select_bool

end oracle_comp
