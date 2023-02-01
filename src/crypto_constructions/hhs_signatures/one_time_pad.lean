/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.primitives.symm_enc
import computational_monads.constructions.repeat
import data.vector.zip
import computational_monads.coercions.instances

/-!
# Symmetric-Key Encryption Schemes

This file defines the one-time pad symmetric encryption scheme,
and proves that it satisfies perfect secrecy.
-/

open oracle_comp oracle_spec

def one_time_pad (n : ℕ) :
  symm_enc_alg (vector bool n) (vector bool n) (vector bool n) :=
{ spec := coin_spec,
  keygen := λ _, oracle_comp.repeat coin n,
  encrypt := λ ⟨m, k⟩, vector.zip_with bxor m k,
  decrypt := λ ⟨c, k⟩, vector.zip_with bxor c k }

namespace one_time_pad

variables {n : ℕ}

@[simp] lemma encrypt_apply (m k : vector bool n) :
  (one_time_pad n).encrypt (m, k) = m.zip_with bxor k := rfl

@[simp] lemma decrypt_apply (c k : vector bool n) :
  (one_time_pad n).decrypt (c, k) = c.zip_with bxor k := rfl

lemma complete (n : ℕ) : (one_time_pad n).complete :=
begin
  refine (one_time_pad n).complete_iff.mpr (λ m k hk, _),
  rw [decrypt_apply, encrypt_apply],
  sorry
end


end one_time_pad