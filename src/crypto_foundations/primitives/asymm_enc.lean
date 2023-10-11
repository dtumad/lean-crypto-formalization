/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.sec_adversary

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.
-/

open oracle_spec oracle_comp
open_locale big_operators

structure asymm_enc_alg (M PK SK C : Type) :=
(keygen : unit → prob_comp (PK × SK))
(encrypt : M × PK → prob_comp C)
(decrypt : C × SK → prob_comp M)

class asymm_enc_alg.efficient {M PK SK C : Type}
  (asymm_enc : asymm_enc_alg M PK SK C) :=
(keygen_poly_time : poly_time_oracle_comp asymm_enc.keygen)
(encrypt_poly_time : poly_time_oracle_comp asymm_enc.encrypt)
(decrypt_poly_time : poly_time_oracle_comp asymm_enc.decrypt)

namespace asymm_enc_alg

variables {M PK SK C : Type}

section sound

def completeness_experiment' (asymm_enc : asymm_enc_alg M PK SK C)
  [decidable_eq M] :
  sec_experiment uniform_selecting uniform_selecting
    (PK × SK) M unit unit unit :=
{ inp_gen := asymm_enc.keygen () ×ₘ return (),
  is_valid := λ ⟨⟨pk, sk⟩, _⟩ ⟨m, _⟩,
    do {σ ← asymm_enc.encrypt (m, pk),
      m' ← asymm_enc.decrypt (σ, sk),
      return (m = m')},
  adv_so := λ _, idₛₒ,
  exp_so := idₛₒ } --

def completeness_experiment (asymm_enc : asymm_enc_alg M PK SK C) [decidable_eq M] :
  soundness_experiment uniform_selecting (PK × SK) M unit :=
{ inp_gen := asymm_enc.keygen (),
  is_valid := λ ⟨pk, sk⟩ m,
    do {σ ← asymm_enc.encrypt (m, pk),
      m' ← asymm_enc.decrypt (σ, sk),
      return (m = m')},
  exp_so := idₛₒ }

end sound


end asymm_enc_alg

def asymm_enc_scheme (M PK SK C : ℕ → Type) :=
Π (sp : ℕ), asymm_enc_alg (M sp) (PK sp) (SK sp) (C sp)
