/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.primitives.asymm_encryption.asymm_enc_alg

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.
-/

open oracle_spec oracle_comp
open_locale big_operators ennreal

def asymm_enc_scheme (M PK SK C : ℕ → Type) :=
Π (sp : ℕ), asymm_enc_alg (M sp) (PK sp) (SK sp) (C sp)

namespace asymm_enc_scheme

open asymm_enc_alg

variables {M PK SK C : ℕ → Type}

def ind_cpa (enc_scheme : asymm_enc_scheme M PK SK C) : Prop :=
∀ (adv : Π (sp : ℕ), (enc_scheme sp).ind_cpa_adversary),
  negligable (λ sp, (adv sp).advantage)

end asymm_enc_scheme