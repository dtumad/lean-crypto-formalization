/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.prod
import computational_monads.constructions.uniform_select
import computational_monads.distribution_semantics.mprod
import computational_monads.asymptotics.polynomial_time

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.
-/

open oracle_spec oracle_comp
open_locale classical big_operators

/-- A symmetric-key encryption algorithm is a set of functions `gen`, `encrypt`, and `decrypt`.
The types `M`, `K`, and `C` are the types of the messages, keys, and ciphertexts respectively.
We assume that the `keygen` has a random selection oracle, and the other two are deterministic.

TODO: oracle_algorithm -/
structure symm_enc_alg (M K C : Type) :=
(keygen : unit → oracle_comp unif_spec K)
(encrypt : M × K → C)
(decrypt : C × K → M)
(complete : ∀ (m : M), ∀ k ∈ (keygen ()).support,
  decrypt (encrypt (m, k), k) = m)
-- (keygen_poly_time : poly_time_oracle_comp keygen)
-- (encrypt_poly_time : poly_time encrypt)
-- (decrypt_poly_time : poly_time decrypt)

namespace symm_enc_alg

variables {M K C : Type}

/-- Alias the plain text type of the algorithm for convenience-/
@[inline, reducible] def M (se_alg : symm_enc_alg M K C) : Type := M

/-- Alias the key type of the algorithm for convenience-/
@[inline, reducible] def K (se_alg : symm_enc_alg M K C) : Type := K

/-- Alias the cipher text type of the algorithm for convenience-/
@[inline, reducible] def C (se_alg : symm_enc_alg M K C) : Type := C

variables (se_alg : symm_enc_alg M K C)

/-- Write completeness in terms of the encryption and decryption functions being inverses. -/
lemma right_inverse_encrypt_decrypt : ∀ k ∈ (se_alg.keygen ()).support,
  function.right_inverse (λ m, se_alg.encrypt (m, k)) (λ c, se_alg.decrypt (c, k)) :=
λ k hk m, se_alg.complete m k hk

lemma encrypt_injective (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ m, se_alg.encrypt (m, k) : M → C).injective :=
function.right_inverse.injective (se_alg.right_inverse_encrypt_decrypt k hk)

lemma decrypt_surjective (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ m, se_alg.decrypt (m, k) : C → M).surjective :=
function.right_inverse.surjective (se_alg.right_inverse_encrypt_decrypt k hk)

/-- Due to completeness there must be at least as many ciphertexts as plaintexts. -/
theorem card_message_le_card_ciphertext [fintype M] [fintype C] :
  fintype.card M ≤ fintype.card C :=
let ⟨k, hk⟩ := (se_alg.keygen ()).support_nonempty in -- keygen has at least one possible output
  fintype.card_le_of_injective _ (se_alg.encrypt_injective k hk)

section mgen_and_encrypt

/-- Computation that given a message distribution `m_dist`, will draw a message `m` from the
distribution, generate a key `k` using `keygen`, and calculate the resulting ciphertext `c`.
The computation returns both the chosen message and the resulting ciphertext. -/
@[inline, reducible] def mgen_and_encrypt
  (m_dist : oracle_comp unif_spec M) :
  oracle_comp unif_spec (M × C) :=
do {m ← m_dist, k ← se_alg.keygen (), return (m, se_alg.encrypt (m, k))}

variable (m_dist : oracle_comp unif_spec M)

/-- Possible outputs of `mgen_and_encrypt` as a union over possible messages and keys. -/
lemma support_mgen_and_encrypt' : (se_alg.mgen_and_encrypt m_dist).support =
  ⋃ m ∈ m_dist.support, ⋃ k ∈ (se_alg.keygen ()).support, {(m, se_alg.encrypt (m, k))} :=
by simp only [support_bind, support_return]

/-- Possible outputs of `mgen_and_encrypt` as a union over messages of the image of keys. -/
@[simp] lemma support_mgen_and_encrypt : (se_alg.mgen_and_encrypt m_dist).support =
  ⋃ m ∈ m_dist.support, (λ k, (m, se_alg.encrypt (m, k))) '' (se_alg.keygen ()).support :=
by simp only [support_bind, support_bind_return]

/-- `(m, c)` is a possible output of `mgen_and_encrypt` iff `m` is a possible output of `m_dist`
and there exists a key in the output of `keygen` that encrypts `m` to `c`. -/
lemma mem_support_mgen_and_encrypt_iff (m : M) (c : C) :
  (m, c) ∈ (se_alg.mgen_and_encrypt m_dist).support ↔
    m ∈ m_dist.support ∧ ∃ k ∈ (se_alg.keygen ()).support, se_alg.encrypt (m, k) = c :=
by simp_rw [support_bind, support_return, set.mem_Union, set.mem_singleton_iff,
  prod.eq_iff_fst_eq_snd_eq, exists_and_distrib_left, exists_prop, exists_eq_left', @eq_comm _ c]

/-- Given an output `(m, c)` of `mgen_and_encrypt`, there exists a key `k` in `keygen`'s support
such that `k` encrypts `m` to `c`. -/
lemma exists_key_of_mem_support_mgen_and_encrypt (m : M) (c : C)
  (h : (m, c) ∈ (se_alg.mgen_and_encrypt m_dist).support) :
    ∃ k ∈ (se_alg.keygen ()).support, se_alg.encrypt (m, k) = c :=
((se_alg.mem_support_mgen_and_encrypt_iff m_dist m c).1 h).2

/-- The distribution associated to `mgen_and_encrypt` is the same as that associated to
running `m_dist` and `keygen` independently, and mapping according to the `encrypt` function. -/
lemma mgen_and_encrypt_dist_equiv : se_alg.mgen_and_encrypt m_dist ≃ₚ
  (λ x, (prod.fst x, se_alg.encrypt x)) <$> (prod.mk <$> m_dist <*> se_alg.keygen ()) :=
begin
  rw [mgen_and_encrypt],
  simp [map_seq, function.comp, seq_map_eq_bind_bind],
end

/-- The probability of getting a particular output `(m, c)` from `mgen_and_encrypt` is the sum over
possible keys that encrypt `m` to `c` of the probability of getting that key,
weighted by the probability of getting `m` from the message distribution. -/
lemma eval_dist_mgen_and_encrypt_apply (m : M) (c : C) :
  ⁅= (m, c) | se_alg.mgen_and_encrypt m_dist⁆ =
    ∑' (k : K), if c = se_alg.encrypt (m, k)
      then ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ else 0 :=
begin
  rw [mgen_and_encrypt, prob_output_bind_bind_comm, prob_output_bind_eq_tsum],
  simp only [prob_output_bind_prod_mk_snd', mul_ite, mul_zero, mul_comm ⁅= m | m_dist⁆],
end

/-- The message portion of the output of `mgen_and_encrypt` follows the message distribution. -/
lemma fst_map_mgen_and_encrypt_dist_equiv :
  prod.fst <$> se_alg.mgen_and_encrypt m_dist ≃ₚ m_dist :=
by simp only [dist_equiv.def, pmf.map_comp, eval_dist_map, eval_dist_bind, eval_dist_bind_return,
  pmf.map_bind, prod.fst_comp_mk, pmf.map_const, pmf.bind_pure]

end mgen_and_encrypt

section perfect_secrecy

/-- A symmetric encryption algorithm has perfect secrecy if the probability of any particular
ciphertext is the same, regardless of the plaintext. We express this as the fact that for any
distribution of messages `message_dist`, and fixed message `m` and ciphertext `c`,
the probability of getting `c` from encrypting a message drawn from `message_dist`
is the same as the probability of getting `c` from encrypting the fixed `m`. -/
def perfect_secrecy (se_alg : symm_enc_alg M K C) : Prop :=
∀ (m_dist : oracle_comp unif_spec M) (m : M) (c : C),
  (se_alg.mgen_and_encrypt m_dist).indep_event ((= m) ∘ prod.fst) ((= c) ∘ prod.snd)

/-- Restate perfect secrecy in terms of explicit probabilities instead of indepent events.
A symmetric encryption algorithm has perfect secrecy iff the probability of getting a given
message-ciphertext after generating a key and encrypting is the probability of drawing the message
times the probability of getting that ciphertext from any message, for any message distribution. -/
theorem perfect_secrecy_iff : se_alg.perfect_secrecy ↔ ∀ (m_dist : oracle_comp unif_spec M)
  (m : M) (c : C), ⁅= (m, c) | se_alg.mgen_and_encrypt m_dist⁆ =
    ⁅= m | m_dist⁆ * ⁅= c | prod.snd <$> se_alg.mgen_and_encrypt m_dist⁆ :=
begin
  refine forall_congr (λ m_dist, (forall_congr (λ m, forall_congr (λ c, _)))),
  simp only [indep_event_iff, ← prob_event_map,
    (fst_map_mgen_and_encrypt_dist_equiv se_alg m_dist).prob_event_eq],
  simp only [function.comp_app, prob_event_eq_eq_prob_output_map, id_map', oracle_comp.map_bind,
    snd_map_bind_return, map_map_eq_map_comp, prob_event_fst_eq_snd_eq],
end

section equal_card

variables [fintype M] [fintype K] [fintype C]
  (hmk : fintype.card M = fintype.card K) (hkc : fintype.card K = fintype.card C)
include hmk hkc

/-- If all spaces have the same size we can get bijectivity of encrypt not just injectivity. -/
lemma encrypt_bijective_of_equal_card (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ m, se_alg.encrypt (m, k) : M → C).bijective :=
(fintype.bijective_iff_injective_and_card _).2
  ⟨se_alg.encrypt_injective k hk, hmk.trans hkc⟩

/-- If all spaces have the same size we can get bijectivity of decrypt not just surjectivity. -/
lemma decrypt_bijective_of_equal_card (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ c, se_alg.decrypt (c, k) : C → M).bijective :=
(fintype.bijective_iff_surjective_and_card _).2
  ⟨se_alg.decrypt_surjective k hk, symm $ hmk.trans hkc⟩

/-- If all spaces are the same size then encryption and decryption are also left inverses. -/
lemma left_inverse_encrypt_decrypt : ∀ k ∈ (se_alg.keygen ()).support,
  function.left_inverse (λ m, se_alg.encrypt (m, k)) (λ c, se_alg.decrypt (c, k)) :=
λ k hk c, (se_alg.decrypt_bijective_of_equal_card hmk hkc k hk).1 (se_alg.complete _ _ hk)

/-- Reverse version of completeness, i.e. encrypting a decryption gives the initial value. -/
lemma complete' (c : C) (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  se_alg.encrypt (se_alg.decrypt (c, k), k) = c :=
se_alg.left_inverse_encrypt_decrypt hmk hkc k hk c

section perfect_secrecy

/-- Given perfect secrecy and matching cardinatlities, every message-ciphertext pair must
give rise to a key that encrypts that message to that ciphertext. -/
theorem exists_unique_key_of_perfect_secrecy (h : se_alg.perfect_secrecy) (m : M) (c : C) :
  ∃! (k : K), k ∈ (se_alg.keygen ()).support ∧ se_alg.encrypt (m, k) = c :=
begin
  -- We first show regular existence, and then extend to uniqueness after.
  have hmc : ∀ m c, ∃ k, k ∈ (se_alg.keygen ()).support ∧ se_alg.encrypt (m, k) = c,
  { clear m c, intros m c,
    haveI : nonempty M := ⟨m⟩,
    -- If the message and ciphertext have non-zero probability, there must be an encryption key.
    suffices : 0 < ⁅= (m, c) | se_alg.mgen_and_encrypt ($ᵗ M)⁆,
    from let ⟨k, hk, hk'⟩ := se_alg.exists_key_of_mem_support_mgen_and_encrypt
      ($ᵗ M) m c ((prob_output_pos_iff _ _).1 this) in ⟨k, hk, hk'⟩,
    -- It suffices to show that such a key exists for *some* message, rather than exactly `m`.
    suffices : ∃ m' k, k ∈ (se_alg.keygen ()).support ∧ se_alg.encrypt (m', k) = c,
    by simpa only [(se_alg.perfect_secrecy_iff.1 h) ($ᵗ M) m c, ennreal.mul_pos_iff, true_and,
      prob_output_pos_iff, mem_support_uniform_select_fintype, mem_support_map_snd_iff,
      mem_support_mgen_and_encrypt_iff, mem_support_uniform_select_fintype M, exists_prop],
    -- We can choose an arbitrary key, and then take the message to be the decrypted ciphertext.
    obtain ⟨k, hk⟩ := (se_alg.keygen ()).support_nonempty,
    exact ⟨se_alg.decrypt (c, k), k, hk, se_alg.left_inverse_encrypt_decrypt hmk hkc k hk c⟩ },
  -- Due to the cardinalities this further implies `encrypt` is bijective on the set of keys.
  have : (λ k, se_alg.encrypt (m, k)).bijective := (fintype.bijective_iff_surjective_and_card _).2
    ⟨λ c, let ⟨k, _, hk⟩ := hmc m c in ⟨k, hk⟩, hkc⟩,
  exact exists_unique_of_exists_of_unique (hmc m c) (λ k k' h h', this.1 (h.2.trans h'.2.symm)),
end

/-- Given perfect secrecy and matching cardinatlities, the keygen function must include
all possible keys in its set of possible outputs. -/
lemma support_keygen_of_perfect_secrecy (h : se_alg.perfect_secrecy) :
  (se_alg.keygen ()).support = set.univ :=
begin
  -- If the support is as large as the entire space `K`, it must be the whole space `K`.
  suffices : fintype.card K ≤ (se_alg.keygen ()).support.to_finset.card,
  from set.to_finset_eq_univ.1 (finset.eq_univ_of_card _ $ antisymm (finset.card_le_univ _) this),
  -- Need to handle the case of `M` being an empty type seperately.
  by_cases hM : nonempty M,
  { refine hM.elim (λ m, _),
    calc fintype.card K = fintype.card C : hkc
      ... ≤ ((λ k, se_alg.encrypt (m, k)) '' (se_alg.keygen ()).support).to_finset.card :
        finset.card_le_of_subset (λ c hc, set.mem_to_finset.2 ((set.mem_image _ _ _).2 $
          exists_of_exists_unique (se_alg.exists_unique_key_of_perfect_secrecy hmk hkc h m c)))
      ... ≤ (se_alg.keygen ()).support.to_finset.card :
        by simpa only [set.to_finset_image] using finset.card_image_le },
  { simpa only [← hmk, @fintype.card_eq_zero M _ (not_nonempty_iff.1 hM)] using zero_le' }
end

/-- Given perfect secrecy and matching cardinality, all keys are possible outputs of `keygen`. -/
lemma mem_support_keygen (h : se_alg.perfect_secrecy) (k : K) : k ∈ (se_alg.keygen ()).support :=
(se_alg.support_keygen_of_perfect_secrecy hmk hkc h).symm ▸ set.mem_univ k

/-- If all spaces have the same size we can get bijectivity of encrypt not just injectivity,
where encryption is viewed as a function on keys with a fixed message. -/
lemma encrypt_key_bijective_of_perfect_secrecy (h : se_alg.perfect_secrecy) (m : M) :
  (λ k, se_alg.encrypt (m, k) : K → C).bijective :=
(function.bijective_iff_exists_unique _).2 $
  λ c, let ⟨k, hk, h'⟩ := se_alg.exists_unique_key_of_perfect_secrecy hmk hkc h m c
    in ⟨k, hk.2, λ k' hk', h' k' ⟨se_alg.mem_support_keygen hmk hkc h k', hk'⟩⟩

/-- If all spaces have the same size we can get bijectivity of encrypt not just injectivity,
where decryption is viewed as a function on keys with a fixed ciphertext. -/
lemma decrypt_key_bijective_of_perfect_secrecy (h : se_alg.perfect_secrecy) (c : C) :
  (λ k, se_alg.decrypt (c, k) : K → M).bijective :=
(function.bijective_iff_exists_unique _).2
  (λ m, let ⟨k, hk, h'⟩ := se_alg.exists_unique_key_of_perfect_secrecy hmk hkc h m c
    in ⟨k, hk.2 ▸ se_alg.complete m k hk.1, λ k' hk', h' k' ⟨se_alg.mem_support_keygen
      hmk hkc h k', hk' ▸ se_alg.complete' hmk hkc c k' (se_alg.mem_support_keygen hmk hkc h k')⟩⟩)

/-- encrypting and decrypting a message gives the original iff the same key is used. -/
lemma decrypt_encrypt_eq_iff_of_perfect_secrecy (h : se_alg.perfect_secrecy) (m : M) (k k' : K) :
  se_alg.decrypt (se_alg.encrypt (m, k), k') = m ↔ k = k' :=
have hk : k ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k),
have hk' : k' ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k'),
⟨λ h', (se_alg.encrypt_key_bijective_of_perfect_secrecy hmk hkc h m).1
  ((se_alg.decrypt_bijective_of_equal_card hmk hkc k' hk').1
  (h'.trans (se_alg.complete m k' hk').symm)), λ h', h' ▸ se_alg.complete m k hk⟩

/-- decrypting and encrypting a ciphertext gives the original iff the same key is used. -/
lemma encrypt_decrypt_eq_iff_of_perfect_secrecy (h : se_alg.perfect_secrecy) (c : C) (k k' : K) :
  se_alg.encrypt (se_alg.decrypt (c, k), k') = c ↔ k = k' :=
have hk : k ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k),
have hk' : k' ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k'),
⟨λ h', (se_alg.decrypt_key_bijective_of_perfect_secrecy hmk hkc h c).1
  ((se_alg.encrypt_bijective_of_equal_card hmk hkc k' hk').1
  (h'.trans (se_alg.complete' hmk hkc c k' hk').symm)), λ h', h' ▸ se_alg.complete' hmk hkc c k hk⟩

lemma eval_dist_ciphertext_eq_eval_dist_key_of_perfect_secrecy
  (h : se_alg.perfect_secrecy) (m_dist : oracle_comp unif_spec M)
  (k : K) (c : C) (h' : se_alg.decrypt (c, k) ∈ m_dist.support) :
  ⁅= c | prod.snd <$> se_alg.mgen_and_encrypt m_dist⁆ = ⁅= k | se_alg.keygen ()⁆ :=
begin
  -- Multiply by the probability of getting the decryption, in order to use perfect secrecy
  let m := se_alg.decrypt (c, k),
  suffices : ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ =
    ⁅= m | m_dist⁆ * ⁅= c | prod.snd <$> se_alg.mgen_and_encrypt m_dist⁆,
  from ((ennreal.mul_eq_mul_left (prob_output_ne_zero h')
    (pmf.apply_ne_top _ _)).1 this).symm,
  -- Extend the encryption function to include a side message, preserving injectivity.
  let f : M × K → M × C := λ x, (x.1, se_alg.encrypt (x.1, x.2)),
  have hf : f (m, k) = (m, c) := prod.eq_iff_fst_eq_snd_eq.2
    ⟨rfl, se_alg.complete' hmk hkc c k $ se_alg.mem_support_keygen hmk hkc h k⟩,
  have hf' : f.injective,
  { simp only [function.injective, prod.eq_iff_fst_eq_snd_eq] at ⊢,
    exact λ x y hxy, ⟨hxy.1, (se_alg.encrypt_key_bijective_of_perfect_secrecy
      hmk hkc h x.1).1 $ hxy.2.trans (hxy.1 ▸ rfl)⟩ },
  -- Using the above function we can move from keys to ciphertexts, then apply perfect secrecy.
  calc ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ =
    ⁅= (m, k) | prod.mk <$> m_dist <*> se_alg.keygen ()⁆ :
      symm (prob_output_seq_map_eq_mul_of_injective2 _ _ prod.mk_injective2 _ _)
    ... = ⁅= f (m, k) | f <$> (prod.mk <$> m_dist <*> se_alg.keygen ())⁆ :
      (prob_output_map_of_injective _ f (m, k) hf').symm
    ... = ⁅= (m, c) | se_alg.mgen_and_encrypt m_dist⁆ :
      by simp_rw [hf, map_seq, mgen_and_encrypt, seq_map_eq_bind_bind, oracle_comp.bind_map]
    ... = ⁅= m | m_dist⁆ * ⁅= c | prod.snd <$> se_alg.mgen_and_encrypt m_dist⁆ :
      (se_alg.perfect_secrecy_iff.1 h) m_dist m c
end

/-- Assuming that the message, key, and ciphertext spaces all have the same size,
any system with perfect secrecy must generate keys uniformly at random. -/
theorem eval_dist_keygen_eq_uniform_of_perfect_secrecy [nonempty M] [nonempty C]
  (h : se_alg.perfect_secrecy) (k : K) : ⁅= k | se_alg.keygen ()⁆ = (fintype.card K)⁻¹ :=
calc ⁅= k | se_alg.keygen ()⁆ = 1 * ⁅= k | se_alg.keygen ()⁆ : (one_mul _).symm
  -- Introduce a copy of `fintype.card C` by multiplying by its inverse.
  ... = ((fintype.card C)⁻¹ * (fintype.card C)) * ⁅= k | se_alg.keygen ()⁆ :
    congr_arg (λ x, x * ⁅= k | se_alg.keygen ()⁆) ((ennreal.inv_mul_cancel (nat.cast_ne_zero.2
      fintype.card_ne_zero) $ by simp only [ne.def, ennreal.nat_ne_top, not_false_iff]).symm)
  -- Multiplication by `fintype.card C` is equivalent to summing over `C` itself.
  ... = (fintype.card C)⁻¹ * (∑' (c : C), ⁅= k | se_alg.keygen ()⁆) :
    by simp only [tsum_fintype, finset.sum_const, fintype.card, ←mul_assoc, nsmul_eq_mul]
  -- For any `c : C`, the probability of getting `c` is equal to getting `k` (by above).
  ... = (fintype.card C)⁻¹ * (∑' (c : C), ⁅= c | prod.snd <$> se_alg.mgen_and_encrypt ($ᵗ M)⁆) :
    congr_arg (λ x, (fintype.card C)⁻¹ * x) (tsum_congr $ λ c, symm $
      se_alg.eval_dist_ciphertext_eq_eval_dist_key_of_perfect_secrecy hmk hkc h _ k c
        (mem_support_uniform_select_fintype _ _))
  -- The sum over all `c : C` of the probability of getting that value is just `1`.
  ... = (fintype.card C)⁻¹ : by rw [tsum_prob_output, mul_one]
  ... = (fintype.card K)⁻¹ : by rw hkc

/-- Given that all spaces have the same cardinality, perfect secrecy holds iff:
1. `keygen` chooses keys uniformly at random.
2. for every message `m` and ciphertext `c`, there is a unique key encrypting `m` to `c`.
In particular this will be used to show perfect secrecy of the one-time pad.-/
theorem perfect_secrecy_iff_of_equal_card [nonempty M] [nonempty C] :
  se_alg.perfect_secrecy ↔ (∀ k, ⁅= k | se_alg.keygen ()⁆ = (fintype.card K)⁻¹) ∧
    (∀ m c, ∃! k, k ∈ (se_alg.keygen ()).support ∧ se_alg.encrypt (m, k) = c) :=
begin
  split,
  { exact λ h, ⟨se_alg.eval_dist_keygen_eq_uniform_of_perfect_secrecy hmk hkc h,
      λ m c, se_alg.exists_unique_key_of_perfect_secrecy hmk hkc h m c⟩ },
  { rw [perfect_secrecy_iff],
    rintros ⟨h_keygen, h_encrypt⟩ m_dist m c,
    obtain ⟨k, ⟨⟨_, hc⟩, hk⟩⟩ := h_encrypt m c,
    have : ∀ m', ⁅= (m', c) | se_alg.mgen_and_encrypt m_dist⁆ =
      ⁅= m' | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ :=
    begin
      refine λ m', (se_alg.eval_dist_mgen_and_encrypt_apply _ _ _).trans _,
      obtain ⟨k', hks, hke⟩ := h_encrypt m' c,
      refine trans (tsum_eq_single k' $ λ k'' hk'', _) _,
      { by_cases hks' : k'' ∈ (se_alg.keygen ()).support,
        { exact ite_eq_right_iff.2 (λ hkkd, false.elim (hk'' $ hke k'' ⟨hks', hkkd.symm⟩)) },
        { simp_rw [(prob_output_eq_zero_iff _ _).2 hks', mul_zero, if_t_t] } },
      { simp_rw [hks.2, eq_self_iff_true, if_true, h_keygen] },
    end,
    calc ⁅= (m, c) | se_alg.mgen_and_encrypt m_dist⁆ =
      ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ : this m
      ... = ⁅= m | m_dist⁆ * ∑' m', ⁅= m' | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ :
        by rw [ennreal.tsum_mul_right, tsum_prob_output, one_mul]
      ... = ⁅= m | m_dist⁆ * ∑' m', ⁅= (m', c) | se_alg.mgen_and_encrypt m_dist⁆ :
        congr_arg (λ x, _ * x) (tsum_congr $ λ m', (this m').symm)
      ... = ⁅= m | m_dist⁆ * ⁅= c | prod.snd <$> se_alg.mgen_and_encrypt m_dist⁆ :
        begin
          simp_rw [prob_output_map_eq_tsum_ite, ennreal.tsum_prod', ← hc],
          exact congr_arg (λ x, _ * x) (tsum_congr (λ m', symm $ trans
            (tsum_eq_single (se_alg.encrypt (m, k)) $ λ c hc, if_neg hc.symm) (if_pos rfl))),
        end
  }
end

end perfect_secrecy

end equal_card

end perfect_secrecy

end symm_enc_alg