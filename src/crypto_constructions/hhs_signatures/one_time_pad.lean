/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.primitives.symm_enc
import computational_monads.constructions.repeat
import computational_monads.coercions.instances

import data.vector.zip

/-!
# Symmetric-Key Encryption Schemes

This file defines the one time pad encryption scheme,
and proves that it satisfies perfect secrecy.
-/

open oracle_comp oracle_spec

def one_time_pad (n : ℕ) : symm_enc_alg (vector bool n) (vector bool n) (vector bool n) :=
{ keygen := λ _, oracle_comp.repeat coin n,
  encrypt := λ ⟨m, k⟩, vector.zip_with bxor m k,
  decrypt := λ ⟨c, k⟩, vector.zip_with bxor c k,
  complete := λ m k _, (vector.ext (λ i, by simp only [vector.zip_with_nth, bool.bxor_assoc,
    bxor_self, bool.bxor_ff_right]) : vector.zip_with bxor (vector.zip_with bxor m k) k = m) }

namespace one_time_pad

variables {n : ℕ}

@[simp] lemma keygen_apply (u : unit) :
  (one_time_pad n).keygen u = oracle_comp.repeat coin n := rfl

@[simp] lemma encrypt_apply (m k : vector bool n) :
  (one_time_pad n).encrypt (m, k) = m.zip_with bxor k := rfl

@[simp] lemma decrypt_apply (c k : vector bool n) :
  (one_time_pad n).decrypt (c, k) = c.zip_with bxor k := rfl

theorem perfect_secrecy (n : ℕ) : (one_time_pad n).perfect_secrecy :=
begin
  refine ((one_time_pad n).perfect_secrecy_iff_of_equal_card rfl rfl).2 ⟨λ v, _, λ m c, _⟩,
  { calc ⁅= v | (one_time_pad n).keygen ()⁆ = (list.map ⁅coin⁆ v.to_list).prod :
        by rw [keygen_apply, eval_dist_repeat_apply, vector.to_list_map, eval_dist_coe_sub_spec]
      ... = 2⁻¹ ^ (list.map ⁅coin⁆ v.to_list).length :
        list.prod_eq_pow_card _ 2⁻¹ (λ x hx, let ⟨y, hy⟩ := list.mem_map.1 hx in
          by simp only [← hy.2, eval_dist_query, pmf.uniform_of_fintype_apply, coin_spec_range,
            fintype.card_bool, nat.cast_bit0, algebra_map.coe_one])
      ... = (fintype.card (vector bool n))⁻¹ : by simp_rw [card_vector, fintype.card_bool,
        nat.cast_pow, nat.cast_two, ennreal.inv_pow, list.length_map, vector.to_list_length] },
  { refine ⟨vector.zip_with bxor m c, ⟨_, _⟩, λ k hk, _⟩,
    { simp only [keygen_apply, mem_support_repeat_iff_forall, support_coe_sub_spec, coin,
        support_query, set.top_eq_univ, set.mem_univ, imp_true_iff] },
    { exact vector.ext (λ i, by simp only [encrypt_apply, vector.zip_with_nth,
        ← bool.bxor_assoc, bxor_self, bool.bxor_ff_left]) },
    { exact vector.ext (λ i, by simp only [hk.2.symm, ← bool.bxor_assoc, encrypt_apply,
        vector.zip_with_nth, bxor_self, bool.bxor_ff_left]) } }
end


end one_time_pad