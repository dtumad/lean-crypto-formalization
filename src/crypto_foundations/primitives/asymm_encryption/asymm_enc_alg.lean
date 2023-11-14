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

/-- Base typeclass for building algorithms with oracle access defined by `spec : oracle_spec`.
On its own just provides a way to simulate computations with the given oracle spec,
but is generally meant to be extended with other computations to define a algorithm.
For example `so` may provide a way to simulate a random oracle. -/
structure simulation_spec (spec : oracle_spec) :=
(S : Type) (so : sim_oracle spec uniform_selecting S)

structure algorithm_base (spec : oracle_spec) :=
(S : Type) (so : sim_oracle spec uniform_selecting S)

noncomputable def simulation_spec.exec {spec : oracle_spec} {α : Type}
  (alg : simulation_spec spec) (oa : oracle_comp spec α) :
  oracle_comp uniform_selecting α :=
dsimulate' alg.so oa

structure asymm_enc_alg' (spec : oracle_spec) (M PK SK C : Type)
  extends algorithm_base spec :=
(keygen : unit → oracle_comp spec (PK × SK))
(encrypt : M × PK → oracle_comp spec C)
(decrypt : C × SK → oracle_comp spec M)


variables {M PK SK C : Type}

class asymm_enc_alg.poly_time (asymm_enc : asymm_enc_alg M PK SK C) :=
(keygen_poly_time : poly_time_oracle_comp asymm_enc.keygen)
(encrypt_poly_time : poly_time_oracle_comp asymm_enc.encrypt)
(decrypt_poly_time : poly_time_oracle_comp asymm_enc.decrypt)

-----------------------
structure sec_experiment' (spec : oracle_spec) (α β : Type) :=
(inp_gen : oracle_comp spec α)
(run : α → oracle_comp spec β)
(is_valid : α × β → bool)

structure sec_experiment'' (spec : oracle_spec) (α β S : Type) :=
(inp_gen : oracle_comp spec α)
(run : α → oracle_comp spec β)
(is_valid : α × β → Prop)
(exp_so : sim_oracle spec uniform_selecting S)

structure sec_experiment₂ (spec : oracle_spec) (α β S : Type)
  extends simulation_spec spec :=
(inp_gen : oracle_comp spec α)
(run : α → oracle_comp spec β)
(is_valid : α × β → Prop)
-- (exp_so : sim_oracle spec uniform_selecting S)

noncomputable def sec_experiment''.exec {spec : oracle_spec} {α β S : Type}
  (exp : sec_experiment'' spec α β S) :
  oracle_comp uniform_selecting (α × β)  :=
dsimulate' exp.exp_so (do
  { x ← exp.inp_gen,
    y ← exp.run x,
    return (x, y) } )

noncomputable def sec_experiment₂.exec {spec : oracle_spec} {α β S : Type}
  (exp : sec_experiment₂ spec α β S) :
  oracle_comp uniform_selecting (α × β)  :=
exp.exec (do
  { x ← exp.inp_gen,
    y ← exp.run x,
    return (x, y) } )

noncomputable def sec_experiment''.advantage
  {spec : oracle_spec} {α β S : Type}
  (exp : sec_experiment'' spec α β S) : ℝ≥0∞ :=
⁅exp.is_valid | exp.exec⁆

noncomputable def sec_experiment'.advantage {spec : oracle_spec} {α β : Type}
  (exp : sec_experiment' spec α β) : ℝ≥0∞ :=
⁅= tt | do {x ← exp.inp_gen, y ← exp.run x,
  return (exp.is_valid (x, y))}⁆
----------------------

namespace asymm_enc_alg

section sound

/-- Generate a random key, then return the result of encrypting and decrypting `m`. -/
noncomputable def soundness_experiment (enc_alg : asymm_enc_alg M PK SK C)
  (m : M) : oracle_comp (uniform_selecting) M := do
{ ⟨pk, sk⟩ ← enc_alg.keygen (),
  σ ← enc_alg.encrypt (m, pk),
  enc_alg.decrypt (σ, sk) }

noncomputable def soundness_experiment'' [decidable_eq M] {spec : oracle_spec}
  (enc_alg : asymm_enc_alg' spec M PK SK C)
  (m : M) : sec_experiment'' spec (PK × SK) M enc_alg.S :=
{ inp_gen := enc_alg.keygen (),
  run := λ ⟨pk, sk⟩, do
    { σ ← enc_alg.encrypt (m, pk),
      enc_alg.decrypt (σ, sk) },
  is_valid := λ ⟨⟨pk, sk⟩, m'⟩, m = m',
  exp_so := enc_alg.so }

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

noncomputable def ind_cpa_experiment
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

noncomputable def ind_cpa_experiment'
  {enc_alg : asymm_enc_alg M PK SK C}
  (adv : enc_alg.ind_cpa_adversary) :
  sec_experiment'' uniform_selecting (PK × bool) bool unit :=
{ inp_gen := do
    { pk ← prod.fst <$> enc_alg.keygen (),
      b ← coin, return (pk, b) },
  run := λ ⟨pk, b⟩, do
    { ⟨m₁, m₂⟩ ← adv.run pk,
      c ← enc_alg.encrypt (if b then m₁ else m₂, pk),
      adv.distinguish (pk, (m₁, m₂), c) },
  is_valid := λ ⟨⟨pk, b⟩, b'⟩, b = b',
  exp_so := idₛₒ }

lemma ind_cpa_experiment_advantage_eq {enc_alg : asymm_enc_alg M PK SK C}
  (adv : enc_alg.ind_cpa_adversary) :
  (ind_cpa_experiment adv).advantage = ⁅= tt | do
    { pk ← prod.fst <$> enc_alg.keygen (),
      ms ← adv.run pk,
      b ←$ᵗ bool,
      c ← enc_alg.encrypt (ite b ms.1 ms.2, pk),
      b' ← adv.distinguish (pk, ms, c),
      return (b = b' : bool) }⁆ :=
begin
  sorry,
end

-- /-- Generate keys, get message choices from adversary,
-- flip a coin, encrypt corresponding message, see if adversary succeeds. -/
-- noncomputable def ind_cpa_experiment (enc_alg : asymm_enc_alg M PK SK C)
--   (adv : enc_alg.ind_cpa_adversary) :
--   oracle_comp uniform_selecting bool := do
-- { pk ← prod.fst <$> enc_alg.keygen (),
--   ms ← adv.run pk, -- Run adversary to get a pair of messages
--   b ←$ᵗ bool, -- Choose which message to encrypt
--   c ← enc_alg.encrypt (if b then ms.1 else ms.2, pk),
--   b' ← adv.distinguish (pk, ms, c),
--   return (b = b') }

-- lemma ind_cpa_experiment_dist_equiv (enc_alg : asymm_enc_alg M PK SK C)
--   (adv : enc_alg.ind_cpa_adversary) : enc_alg.ind_cpa_experiment adv ≃ₚ do
--     { pk ← prod.fst <$> enc_alg.keygen (), ms ← adv.run pk, b ←$ᵗ bool,
--       c ← enc_alg.encrypt (if b then ms.1 else ms.2, pk), b' ← adv.distinguish (pk, ms, c),
--       return (b = b') } := dist_equiv.rfl

namespace ind_cpa_adversary

-- noncomputable def advantage {enc_alg : asymm_enc_alg M PK SK C}
--   (adv : enc_alg.ind_cpa_adversary) : ℝ≥0∞ :=
-- ⁅= tt | enc_alg.ind_cpa_experiment adv⁆

end ind_cpa_adversary

end ind_cpa

end asymm_enc_alg