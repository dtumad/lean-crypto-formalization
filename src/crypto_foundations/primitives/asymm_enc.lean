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
open_locale big_operators ennreal

/-- `asymm_enc_alg M PK SK C` is an asymmetric encryption scheme, with `M` the space of messages,
`PK` and `SK` the public and secret keys, and `C` is the space of ciphertexts.
We assume that decryption can be done with only the secret keys.

TODO: think about ways that we could allow random oracles in a usable way,
assuming that in some cases there are no actual oracles (using `[]ₒ` makes it a hassle).-/
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

-- def completeness_experiment' (asymm_enc : asymm_enc_alg M PK SK C) [decidable_eq M] :
--   sec_experiment uniform_selecting uniform_selecting
--     (PK × SK) M unit unit unit :=
-- { inp_gen := asymm_enc.keygen () ×ₘ return (),
--   is_valid := λ ⟨⟨pk, sk⟩, _⟩ ⟨m, _⟩,
--     do {σ ← asymm_enc.encrypt (m, pk),
--       m' ← asymm_enc.decrypt (σ, sk),
--       return (m = m')},
--   adv_so := λ _, idₛₒ,
--   exp_so := idₛₒ }

def completeness_experiment (asymm_enc : asymm_enc_alg M PK SK C) [decidable_eq M] :
  soundness_experiment uniform_selecting (PK × SK) M unit :=
{ inp_gen := asymm_enc.keygen (),
  is_valid := λ ⟨pk, sk⟩ m,
    do {σ ← asymm_enc.encrypt (m, pk),
      m' ← asymm_enc.decrypt (σ, sk),
      return (m = m')},
  exp_so := idₛₒ }

/-- Generate a random key, then return the result of encrypting and decrypting `m`. -/
def soundness_experiment (enc_alg : asymm_enc_alg M PK SK C)
  (m : M) : oracle_comp uniform_selecting M := do
{ ⟨pk, sk⟩ ← enc_alg.keygen (),
  σ ← enc_alg.encrypt (m, pk),
  enc_alg.decrypt (σ, sk) }

/-- An asymmetric encryption algorithm is sound if messages always decrypt to themselves. -/
def sound (enc_alg : asymm_enc_alg M PK SK C) : Prop :=
∀ m : M, ⁅= m | soundness_experiment enc_alg m⁆ = 1

lemma sound_iff_support_decrypt_eq (enc_alg : asymm_enc_alg M PK SK C) :
  enc_alg.sound ↔ ∀ (m : M) (pk : PK) (sk : SK) (σ : C),
    (pk, sk) ∈ (enc_alg.keygen ()).support →
    σ ∈ (enc_alg.encrypt (m, pk)).support →
    (enc_alg.decrypt (σ, sk)).support = {m} :=
begin
  sorry,
end

end sound

section ind_cpa

/-- `ind_cpa_adversary M PK C` is an adversary for IND-CPA security game on an
asymmetric encryption algorithm with public keys in `PK`, messages in `M`, and ciphertexts in `C`.
Adversary is given a public key and returns a pair of messages that it thinks
it can distinguish the encryption of. It addionally has a `distinguish` function
that given a pair of messages and an encryption, returns whether it is an encryption of
the first message or the second message. -/
structure ind_cpa_adversary {M PK C : Type}
  (enc_alg : asymm_enc_alg M PK SK C) extends
  sec_adversary uniform_selecting PK (M × M) :=
(distinguish : PK × M × M × C → prob_comp bool)

def asymm_enc_alg.ind_cpa_experiment
  (enc_alg : asymm_enc_alg M PK SK C)
  (adv : enc_alg.ind_cpa_adversary) :
  oracle_comp uniform_selecting bool := do
{ ⟨pk, sk⟩ ← enc_alg.keygen (),
  ⟨m₁, m₂⟩ ← adv.run pk, b ← coin,
  c ← enc_alg.encrypt (if b then m₁ else m₂, pk),
  b' ← adv.distinguish ⟨pk, m₁, m₂, c⟩,
  return (b = b') }

namespace ind_cpa_adversary

noncomputable def advantage {enc_alg : asymm_enc_alg M PK SK C}
  (adv : enc_alg.ind_cpa_adversary) : ℝ≥0∞ :=
⁅= tt | enc_alg.ind_cpa_experiment adv⁆ - 1 / 2

end ind_cpa_adversary

end ind_cpa

end asymm_enc_alg

def asymm_enc_scheme (M PK SK C : ℕ → Type) :=
Π (sp : ℕ), asymm_enc_alg (M sp) (PK sp) (SK sp) (C sp)

namespace asymm_enc_scheme

open asymm_enc_alg

variables {M PK SK C : ℕ → Type}

def ind_cpa (enc_scheme : asymm_enc_scheme M PK SK C) : Prop :=
∀ (adv : Π (sp : ℕ), (enc_scheme sp).ind_cpa_adversary),
  negligable (λ sp, (adv sp).advantage)

end asymm_enc_scheme