/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.sec_experiment

/-!
# Assymetric Encryption

This file defines asymmetric encryption algorithms as a type `asymm_enc_alg spec M PK SK C`.
-/

open oracle_spec oracle_comp
open_locale big_operators ennreal

/-- `asymm_enc_alg spec M PK SK C` is an asymmetric encryption scheme,
with `spec` the set of oracles available, `M` the type of messages,
`PK` and `SK` the type of public and secret keys, and `C` is the type of ciphertexts.
We assume that decryption can be done with only the secret keys. -/
structure asymm_enc_alg (spec : oracle_spec) (M PK SK C : Type)
  extends oracle_algorithm spec :=
(keygen : unit → oracle_comp spec (PK × SK))
(encrypt : M × PK → oracle_comp spec C)
(decrypt : C × SK → oracle_comp spec M)

namespace asymm_enc_alg

variables {spec : oracle_spec} {M PK SK C : Type}

section sound

/-- Experiment for checking that an asymmetric encryption algorithm is sound.
`inp_gen` runs the key generation algorithm and returns the keys,
`main` encrypts then decrypts the message `m`, and `is_valid` checks the new message is the same.
The algorithm will be sound if this experiment always succeeds. -/
def soundness_exp (enc_alg : asymm_enc_alg spec M PK SK C)
  (m : M) : sec_exp spec (PK × SK) M :=
{ inp_gen := enc_alg.keygen (),
  main := λ ⟨pk, sk⟩, do
    { σ ← enc_alg.encrypt (m, pk),
      enc_alg.decrypt (σ, sk) },
  is_valid := λ ⟨pk, sk⟩ m', m = m',
  .. enc_alg }

namespace soundness_exp

variables (enc_alg : asymm_enc_alg spec M PK SK C) (m : M)

@[simp] lemma inp_gen_eq : (soundness_exp enc_alg m).inp_gen = enc_alg.keygen () := rfl

@[simp] lemma main_eq (ks : PK × SK) : (soundness_exp enc_alg m).main ks =
  do {σ ← enc_alg.encrypt (m, ks.1), enc_alg.decrypt (σ, ks.2)} :=
match ks with | ⟨pk, sk⟩ := rfl end

@[simp] lemma is_valid_eq (ks : PK × SK) : (soundness_exp enc_alg m).is_valid ks = (=) m :=
match ks with | ⟨pk, sk⟩ := rfl end

@[simp] lemma to_oracle_algorithm_eq : (soundness_exp enc_alg m).to_oracle_algorithm =
  enc_alg.to_oracle_algorithm := rfl

end soundness_exp

/-- An asymmetric encryption algorithm is sound if messages always decrypt to themselves. -/
def is_sound (enc_alg : asymm_enc_alg spec M PK SK C) : Prop :=
∀ m, (soundness_exp enc_alg m).advantage = 1

lemma is_sound_iff (enc_alg : asymm_enc_alg spec M PK SK C) : enc_alg.is_sound ↔
  ∀ (m m': M) (pk : PK) (sk : SK) (s : enc_alg.base_S),
    ((pk, sk), s) ∈ (simulate enc_alg.base_oracle (enc_alg.keygen ()) enc_alg.init_state).support →
  ∀ σ s', (σ, s') ∈ (simulate enc_alg.base_oracle (enc_alg.encrypt (m, pk)) s).support →
  ∀ s'', (m', s'') ∈ (simulate enc_alg.base_oracle (enc_alg.decrypt (σ, sk)) s').support →
    m' = m :=
by simp only [is_sound, sec_exp.advantage_eq_prob_event, sec_exp.run_def, set.mem_image,
  prob_output_eq_one_iff_subset, set.subset_def, soundness_exp.to_oracle_algorithm_eq,
  soundness_exp.inp_gen_eq, soundness_exp.main_eq, oracle_algorithm.exec_bind, simulate'_bind,
  simulate_bind, simulate'_return, soundness_exp.is_valid_eq, prob_event_eq_eq_prob_output_map',
  oracle_comp.map_bind, snd_map_bind_return, support_bind, support_map, set.mem_Union, prod.exists,
  exists_and_distrib_right, exists_eq_right, set.mem_singleton_iff, forall_exists_index]

end sound

section ind_cpa

/-- `ind_cpa_adversary M PK C` is an adversary for IND-CPA security game on an
asymmetric encryption algorithm with public keys in `PK`, messages in `M`, and ciphertexts in `C`.
Adversary is given a public key and returns a pair of messages that it thinks
it can distinguish the encryption of. It addionally has a `distinguish` function
that given a pair of messages and an encryption, returns whether it is an encryption of
the first message or the second message. -/
structure ind_cpa_adv (enc_alg : asymm_enc_alg spec M PK SK C)
  extends sec_adv spec PK (M × M) :=
(distinguish : PK × (M × M) × C → oracle_comp spec bool)
(distinguish_qb : query_count spec)

variable {enc_alg : asymm_enc_alg spec M PK SK C}

/-- Experiment for IND-CPA security of an asymmetric encryption algorithm.
`inp_gen` generates a key and pre-selects a random boolean value.
`main` runs the adversary on the public key, and encrypts the resulting message corresponding to
the boolean chosen in `inp_gen`, finally asking the adversary to determine the boolean
given the messages and resulting ciphertext. `is_valid` checks that this choice is correct.
The simulation oracles are pulled in directly from the encryption algorithm. -/
def ind_cpa_exp [is_sub_spec coin_spec spec]
  (adv : enc_alg.ind_cpa_adv) :
  sec_exp spec (PK × bool) bool :=
{ inp_gen := do
    { b ← coin, pk ← prod.fst <$> enc_alg.keygen (),
      return (pk, b) },
  main := λ ⟨pk, b⟩, do
    { ⟨m₁, m₂⟩ ← adv.run pk,
      c ← enc_alg.encrypt (if b then m₁ else m₂, pk),
      adv.distinguish (pk, (m₁, m₂), c) },
  is_valid := λ ⟨pk, b⟩ b', b = b',
  .. enc_alg } -- Pull in the algorithm's oracles

namespace ind_cpa_exp

variables [is_sub_spec coin_spec spec] (adv : enc_alg.ind_cpa_adv)

@[simp] lemma inp_gen_eq : (ind_cpa_exp adv).inp_gen =
  do {b ← coin, pk ← prod.fst <$> enc_alg.keygen (), return (pk, b) } := rfl

@[simp] lemma main_eq : (ind_cpa_exp adv).main =
  λ z, do {ms ← adv.run z.1, c ← enc_alg.encrypt (if z.2 then ms.1 else ms.2, z.1),
    adv.distinguish (z.1, ms, c)} :=
begin
  refine funext (λ z, prod.rec_on z (λ _ _, _)),
  simp only [ind_cpa_exp, prod.mk.eta],
  congr' 1,
  exact funext (λ ms, prod.rec_on ms (λ _ _, rfl)),
end

@[simp] lemma is_valid_eq : (ind_cpa_exp adv).is_valid =
  λ z b', z.2 = b' := funext (λ z, prod.rec_on z (λ _ _, rfl))

@[simp] lemma to_oracle_algorithm_eq : (ind_cpa_exp adv).to_oracle_algorithm =
  enc_alg.to_oracle_algorithm := rfl

@[simp] lemma run_eq : (ind_cpa_exp adv).run = enc_alg.exec
  (do {b ← coin, pk ← prod.fst <$> enc_alg.keygen (),
    ms ← adv.run pk, c ← enc_alg.encrypt (if b then ms.1 else ms.2, pk),
    b' ← adv.distinguish (pk, ms, c), return ((pk, b), b')}) :=
by simp [sec_exp.run, bind_assoc]

lemma prob_event_eq_eq_prob_output_tt {α β : Type} [decidable_eq β] (oa : oracle_comp spec α)
  (f g : α → β) : ⁅λ x, f x = g x | oa⁆ = ⁅= tt | (λ x, (f x = g x : bool)) <$> oa⁆ :=
begin
  rw [prob_output_map_eq_tsum_indicator],
  simp [set.preimage, prob_event_eq_tsum_indicator'],
end

lemma advantage_eq : (ind_cpa_exp adv).advantage =
  ⁅= tt | enc_alg.exec (do
    { b ← coin,
      pk ← prod.fst <$> enc_alg.keygen (),
      ms ← adv.run pk,
      c ← enc_alg.encrypt (ite b ms.1 ms.2, pk),
      b' ← adv.distinguish (pk, ms, c),
      return (b = b' : bool) })⁆ :=
begin
  rw [sec_exp.advantage, run_eq],
  simp [prob_event_eq_eq_prob_output_tt],
end

end ind_cpa_exp

end ind_cpa

end asymm_enc_alg

def asymm_enc_scheme (spec : ℕ → oracle_spec) (M PK SK C : ℕ → Type) :=
Π (sp : ℕ), asymm_enc_alg (spec sp) (M sp) (PK sp) (SK sp) (C sp)

namespace asymm_enc_scheme

open asymm_enc_alg

variables {spec : ℕ → oracle_spec} {M PK SK C : ℕ → Type}
  [∀ sp, coin_spec ⊂ₒ spec sp]

def ind_cpa_secure (enc_scheme : asymm_enc_scheme spec M PK SK C) : Prop :=
∀ (adv : Π (sp : ℕ), (enc_scheme sp).ind_cpa_adv),
  asymptotics.negligible (λ sp, (ind_cpa_exp (adv sp)).advantage)

end asymm_enc_scheme
