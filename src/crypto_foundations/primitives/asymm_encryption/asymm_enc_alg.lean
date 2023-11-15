/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.sec_adversary
import crypto_foundations.sec_experiment

/-!
# Assymetric Encryption

This file defines asymmetric encryption algorithms as a type `asymm_enc_alg spec M PK SK C`.
-/

open oracle_spec oracle_comp
open_locale big_operators ennreal

/-- `asymm_enc_alg M PK SK C` is an asymmetric encryption scheme, with `M` the space of messages,
`PK` and `SK` the public and secret keys, and `C` is the space of ciphertexts.
We assume that decryption can be done with only the secret keys. -/
-- structure asymm_enc_alg (M PK SK C : Type) :=
-- (keygen : unit → oracle_comp uniform_selecting (PK × SK))
-- (encrypt : M × PK → oracle_comp uniform_selecting C)
-- (decrypt : C × SK → oracle_comp uniform_selecting M)
structure asymm_enc_alg (spec : oracle_spec) (M PK SK C : Type)
  extends oracle_algorithm spec :=
(keygen : unit → oracle_comp spec (PK × SK))
(encrypt : M × PK → oracle_comp spec C)
(decrypt : C × SK → oracle_comp spec M)

variables {spec : oracle_spec} {M PK SK C : Type}

namespace asymm_enc_alg

section sound

/-- Experiment for checking that an asymmetric encryption algorithm is sound.
`inp_gen` runs the key generation algorithm and returns the keys,
`main` encrypts then decrypts the message `m`, and `is_valid` checks the new message is the same.
The algorithm will be sound if this experiment always succeeds. -/
noncomputable def soundness_experiment
  (enc_alg : asymm_enc_alg spec M PK SK C) (m : M) :
  sec_experiment spec (PK × SK) M :=
{ inp_gen := enc_alg.keygen (),
  main := λ ⟨pk, sk⟩, do
    { σ ← enc_alg.encrypt (m, pk),
      enc_alg.decrypt (σ, sk) },
  is_valid := λ ⟨⟨pk, sk⟩, m'⟩, m' = m,
  .. enc_alg }

/-- An asymmetric encryption algorithm is sound if messages always decrypt to themselves. -/
def sound (enc_alg : asymm_enc_alg spec M PK SK C) : Prop :=
∀ m, (soundness_experiment enc_alg m).advantage = 1

-- TODO: wrong without simulation
lemma sound_iff_support_decrypt_eq (enc_alg : asymm_enc_alg spec M PK SK C) :
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
structure ind_cpa_adversary (enc_alg : asymm_enc_alg spec M PK SK C) :=
(run : PK → oracle_comp spec (M × M))
(distinguish : PK × (M × M) × C → oracle_comp spec bool)

variable {enc_alg : asymm_enc_alg spec M PK SK C}

/-- Experiment for IND-CPA security of an asymmetric encryption algorithm.
`inp_gen` generates a key and pre-selects a random boolean value.
`main` runs the adversary on the public key, and encrypts the resulting message corresponding to
the boolean chosen in `inp_gen`, finally asking the adversary to determine the boolean
given the messages and resulting ciphertext. `is_valid` checks that this choice is correct.
The simulation oracles are pulled in directly from the encryption algorithm. -/
noncomputable def ind_cpa_experiment [is_sub_spec uniform_selecting spec]
  (adv : enc_alg.ind_cpa_adversary) :
  sec_experiment spec (PK × bool) bool :=
{ inp_gen := do
    { pk ← prod.fst <$> enc_alg.keygen (),
      b ←$ᵗ bool, return (pk, b) },
  main := λ ⟨pk, b⟩, do
    { ⟨m₁, m₂⟩ ← adv.run pk,
      c ← enc_alg.encrypt (if b then m₁ else m₂, pk),
      adv.distinguish (pk, (m₁, m₂), c) },
  is_valid := λ ⟨⟨pk, b⟩, b'⟩, b = b',
  .. enc_alg
}

namespace ind_cpa_experiment

-- lemma ind_cpa_experiment_advantage_eq {enc_alg : asymm_enc_alg M PK SK C}
--   (adv : enc_alg.ind_cpa_adversary) :
--   (ind_cpa_experiment adv).advantage = ⁅= tt | do
--     { pk ← prod.fst <$> enc_alg.keygen (),
--       ms ← adv.run pk,
--       b ←$ᵗ bool,
--       c ← enc_alg.encrypt (ite b ms.1 ms.2, pk),
--       b' ← adv.distinguish (pk, ms, c),
--       return (b = b' : bool) }⁆ :=
-- begin
--   sorry,
-- end

end ind_cpa_experiment

end ind_cpa

end asymm_enc_alg