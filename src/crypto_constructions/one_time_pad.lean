/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.primitives.symm_enc
import computational_monads.constructions.repeat
import data.vector.zip

/-!
# Symmetric-Key Encryption Schemes

This file defines the one time pad encryption scheme,
and proves that it satisfies perfect secrecy.
-/

open oracle_comp oracle_spec

noncomputable def one_time_pad (n : ℕ) :
  symm_enc_alg (vector bool n) (vector bool n) (vector bool n) :=
{ keygen := λ _, $ᵗ (vector bool n), -- random bit-string
  encrypt := λ ⟨m, k⟩, vector.zip_with bxor m k,
  decrypt := λ ⟨c, k⟩, vector.zip_with bxor c k,
  complete := λ m k _, (vector.ext (λ i, by simp [vector.zip_with_nth]) :
    vector.zip_with bxor (vector.zip_with bxor m k) k = m) }

namespace one_time_pad

variables {n : ℕ}

@[simp] lemma keygen_apply (u : unit) :
  (one_time_pad n).keygen u = $ᵗ (vector bool n) := rfl

@[simp] lemma encrypt_apply (m k : vector bool n) :
  (one_time_pad n).encrypt (m, k) = m.zip_with bxor k := rfl

@[simp] lemma decrypt_apply (c k : vector bool n) :
  (one_time_pad n).decrypt (c, k) = c.zip_with bxor k := rfl

lemma zip_with_bxor_comm (xs ys zs : vector bool n) :
  vector.zip_with bxor xs ys = zs ↔ vector.zip_with bxor xs zs = ys :=
by refine ⟨λ h, _, λ h, _⟩; { rw [← h], ext i, simp [← bool.bxor_assoc] }

theorem perfect_secrecy (n : ℕ) : (one_time_pad n).perfect_secrecy :=
((one_time_pad n).perfect_secrecy_iff_of_equal_card rfl rfl).2
  ⟨by simp, λ m c, by simp [zip_with_bxor_comm m _ c]⟩

end one_time_pad