/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.sec_adversary

/-!
# Assymetric Encryption

This file defines asymmetric encryption algorithms in a type `asymm_enc_alg M PK SK C`.
-/

open oracle_spec oracle_comp
open_locale big_operators ennreal

/-- `asymm_enc_alg M PK SK C` is an asymmetric encryption scheme, with `M` the space of messages,
`PK` and `SK` the public and secret keys, and `C` is the space of ciphertexts.
We assume that decryption can be done with only the secret keys. -/
structure asymm_enc_alg (M PK SK C : Type) :=
(keygen : unit → oracle_comp uniform_selecting (PK × SK))
(encrypt : M × PK → oracle_comp uniform_selecting C)
(decrypt : C × SK → oracle_comp uniform_selecting M)

variables {M PK SK C : Type}

class asymm_enc_alg.poly_time (asymm_enc : asymm_enc_alg M PK SK C) :=
(keygen_poly_time : poly_time_oracle_comp asymm_enc.keygen)
(encrypt_poly_time : poly_time_oracle_comp asymm_enc.encrypt)
(decrypt_poly_time : poly_time_oracle_comp asymm_enc.decrypt)

namespace asymm_enc_alg

section sound

/-- Generate a random key, then return the result of encrypting and decrypting `m`. -/
def soundness_experiment (enc_alg : asymm_enc_alg M PK SK C)
  (m : M) : oracle_comp (uniform_selecting ++ ∅) M := do
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
-- structure ind_cpa_adversary (enc_alg : asymm_enc_alg M PK SK C)
--   extends sec_adversary ∅ PK (M × M) :=
-- (distinguish : PK × (M × M) × C → oracle_comp uniform_selecting bool)
structure ind_cpa_adversary (enc_alg : asymm_enc_alg M PK SK C) :=
(run : PK → oracle_comp uniform_selecting (M × M))
(distinguish : PK × (M × M) × C → oracle_comp uniform_selecting bool)


structure sec_experiment' (spec : oracle_spec) (α β : Type) :=
(inp_gen : oracle_comp spec α)
(run : α → oracle_comp spec β)
(is_valid : α × β → bool)

noncomputable def advantage' {spec : oracle_spec} {α β : Type}
  (exp : sec_experiment' spec α β) : ℝ≥0∞ :=
⁅= tt | do {x ← exp.inp_gen, y ← exp.run x,
  return (exp.is_valid (x, y))}⁆

noncomputable def ind_cpa_experiment'
  {enc_alg : asymm_enc_alg M PK SK C}
  (adv : enc_alg.ind_cpa_adversary) :
  sec_experiment' uniform_selecting (PK × bool) bool :=
{ inp_gen := do
    { pk ← prod.fst <$> enc_alg.keygen (),
      b ←$ᵗ bool, return (pk, b) },
  run := λ ⟨pk, b⟩, do
    { ⟨m₁, m₂⟩ ← adv.run pk,
      c ← enc_alg.encrypt (if b then m₁ else m₂, pk),
      adv.distinguish (pk, (m₁, m₂), c) },
  is_valid := λ ⟨⟨pk, b⟩, b'⟩, b = b' }

/-- Generate keys, get message choices from adversary,
flip a coin, encrypt corresponding message, see if adversary succeeds. -/
noncomputable def ind_cpa_experiment (enc_alg : asymm_enc_alg M PK SK C)
  (adv : enc_alg.ind_cpa_adversary) :
  oracle_comp uniform_selecting bool := do
{ pk ← prod.fst <$> enc_alg.keygen (),
  ms ← adv.run pk, -- Run adversary to get a pair of messages
  b ←$ᵗ bool, -- Choose which message to encrypt
  c ← enc_alg.encrypt (if b then ms.1 else ms.2, pk),
  b' ← adv.distinguish (pk, ms, c),
  return (b = b') }

lemma ind_cpa_experiment_dist_equiv (enc_alg : asymm_enc_alg M PK SK C)
  (adv : enc_alg.ind_cpa_adversary) : enc_alg.ind_cpa_experiment adv ≃ₚ do
    { pk ← prod.fst <$> enc_alg.keygen (), ms ← adv.run pk, b ←$ᵗ bool,
      c ← enc_alg.encrypt (if b then ms.1 else ms.2, pk), b' ← adv.distinguish (pk, ms, c),
      return (b = b') } := dist_equiv.rfl

namespace ind_cpa_adversary

noncomputable def advantage {enc_alg : asymm_enc_alg M PK SK C}
  (adv : enc_alg.ind_cpa_adversary) : ℝ≥0∞ :=
⁅= tt | enc_alg.ind_cpa_experiment adv⁆

end ind_cpa_adversary

end ind_cpa

end asymm_enc_alg