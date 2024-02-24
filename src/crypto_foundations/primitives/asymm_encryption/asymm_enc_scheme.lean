/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.primitives.asymm_encryption.asymm_enc_alg

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.

TODO: combine with base file
-/

open oracle_spec oracle_comp
open_locale big_operators ennreal

def asymm_enc_scheme (spec : ℕ → oracle_spec) (M PK SK C : ℕ → Type) :=
Π (sp : ℕ), asymm_enc_alg (spec sp) (M sp) (PK sp) (SK sp) (C sp)

namespace asymm_enc_scheme

open asymm_enc_alg

variables {spec : ℕ → oracle_spec} {M PK SK C : ℕ → Type}
  [∀ sp, coin_spec ⊂ₒ spec sp]

def ind_cpa_secure (enc_scheme : asymm_enc_scheme spec M PK SK C) : Prop :=
∀ (adv : Π (sp : ℕ), (enc_scheme sp).ind_cpa_adv),
  negligable (λ sp, (ind_cpa_exp (adv sp)).advantage)

end asymm_enc_scheme