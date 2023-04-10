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
# Examples Used in the Oakland Poster Presentation

Some examples used in making the S&P poster. Mostly a simplified one time pad
-/

-- %%% Explicit Distribution Semantics %%%
-- (return x).support := {x}
-- ⁅= y | return x⁆ := if y = x then 1 else 0
-- ⁅e | return x⁆ := if x ∈ e then 1 else 0

-- (oa >>= ob).support := ⋃ x ∈ oa.support, (ob x).support
-- ⁅= y | oa >>= ob⁆ := ∑' x, ⁅= x | oa⁆ * ⁅= y | ob x⁆
-- ⁅e | oa >>= ob⁆ := ∑' x, ⁅= x | oa⁆ * ⁅ e | ob x⁆

-- (query i t).support := set.univ
-- ⁅= u | query i t⁆ := 1 / (spec.range i).card
-- ⁅e | query i t⁆ := e.card / (spec.range i).card

namespace oracle_comp

open oracle_spec

open_locale classical

@[inline, reducible] def flip_coin := coin
@[inline, reducible] def xor := bxor

@[simp] lemma zip_with_zip_with_bxor_eq_self {n : ℕ} (m k : vector bool n) :
  vector.zip_with bxor (vector.zip_with bxor m k) k = m := vector.ext (λ _, by simp)

variables {α β γ : Type} {spec : oracle_spec} {n : ℕ}

structure symm_enc_alg :=
(M K C : Type)
(keygen : unit → oracle_comp uniform_selecting K)
(encrypt : M × K → C)
(decrypt : C × K → M)

def one_time_pad (n : ℕ) : symm_enc_alg :=
{ M := vector bool n, -- Messages are bitvecs
  K := vector bool n, -- Keys are bitvecs
  C := vector bool n, -- Ciphertexts are bitvecs
  keygen := λ _, repeat flip_coin n, -- flip `n` coins
  encrypt := λ ⟨m, sk⟩, vector.zip_with xor m sk,
  decrypt := λ ⟨σ, sk⟩, vector.zip_with xor σ sk }

@[simp] lemma keygen_apply (u : unit) :
  (one_time_pad n).keygen u = oracle_comp.repeat coin n := rfl

@[simp] lemma encrypt_apply (m k : vector bool n) :
  (one_time_pad n).encrypt (m, k) = m.zip_with bxor k := rfl

@[simp] lemma decrypt_apply (c k : vector bool n) :
  (one_time_pad n).decrypt (c, k) = c.zip_with bxor k := rfl

@[inline, reducible] def encrypt_then_decrypt (m : vector bool n) :=
let OTP := one_time_pad n in
do{ k ← OTP.keygen (),
    σ ← return (OTP.encrypt (m, k)),
    return (OTP.decrypt (σ, k)) }

-- Encrypting and Decrypting always cancel out.
theorem one_time_pad.complete (m : vector bool n) :
  ⁅= m | encrypt_then_decrypt m⁆ = 1 :=
by simp -- Automatically proven by simplifier.

end oracle_comp