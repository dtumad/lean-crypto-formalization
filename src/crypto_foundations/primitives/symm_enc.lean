/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.independence
import computational_monads.constructions.uniform_select
import computational_monads.constructions.product
import computational_monads.support.prod

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.
-/

open oracle_spec oracle_comp
open_locale classical big_operators

/-- A symmetric-key encryption algorithm is a set of functions `gen`, `encrypt`, and `decrypt`.
The types `M`, `K`, and `C` are the types of the messages, keys, and ciphertexts respectively.
We assume that the `keygen` has a random selection oracle, and the other two are deterministic. -/
structure symm_enc_alg (M K C : Type) :=
(keygen : unit → oracle_comp uniform_selecting K)
(encrypt : M × K → C)
(decrypt : C × K → M)
-- (keygen_poly_time : poly_time_oracle_comp keygen)
-- (encrypt_poly_time : poly_time_oracle_comp encrypt)
-- (decrypt_poly_time : poly_time_oracle_comp decrypt)
(complete : ∀ (m : M), ∀ k ∈ (keygen ()).support, decrypt (encrypt (m, k), k) = m)

namespace symm_enc_alg

/-- Alias the plain text type of the algorithm for convenience-/
@[inline, reducible] def M {M K C : Type} (se_alg : symm_enc_alg M K C) : Type := M

/-- Alias the key type of the algorithm for convenience-/
@[inline, reducible] def K {M K C : Type} (se_alg : symm_enc_alg M K C) : Type := K

/-- Alias the cipher text type of the algorithm for convenience-/
@[inline, reducible] def C {M K C : Type} (se_alg : symm_enc_alg M K C) : Type := C

variables {M K C : Type} (se_alg : symm_enc_alg M K C)

/-- Write completeness in terms of the encryption and decryption functions being inverses. -/
lemma right_inverse_encrypt_decrypt : ∀ k ∈ (se_alg.keygen ()).support,
  function.right_inverse (λ m, se_alg.encrypt (m, k)) (λ c, se_alg.decrypt (c, k)) :=
λ k hk m, se_alg.complete m k hk

lemma encrypt_injective (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ m, se_alg.encrypt (m, k)).injective :=
function.right_inverse.injective (se_alg.right_inverse_encrypt_decrypt k hk)

lemma decrypt_surjective (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ m, se_alg.decrypt (m, k)).surjective :=
function.right_inverse.surjective (se_alg.right_inverse_encrypt_decrypt k hk)

/-- Due to completeness there must be at least as many ciphertexts as plaintexts. -/
theorem card_message_le_card_cipher [fintype M] [fintype C] :
  fintype.card M ≤ fintype.card C :=
let ⟨k, hk⟩ := (se_alg.keygen ()).support_nonempty in -- keygen has at least one possible output
  fintype.card_le_of_injective _ (se_alg.encrypt_injective k hk)

section mgen_encrypt

/-- Computation that given a message `m`, generates a key `k`, and then encrypts the message,
returning both the generated message and the generated ciphertext `c`. -/
@[inline, reducible] def mgen_encrypt (se_alg : symm_enc_alg M K C)
  (m_dist : oracle_comp uniform_selecting M) : oracle_comp uniform_selecting (M × C) :=
do {m ← m_dist,
    k ← se_alg.keygen (),
    return (m, se_alg.encrypt (m, k))}

variable (m_dist : oracle_comp uniform_selecting M)

/-- support of `mgen_encrypt` is the union over possible messages and keys of the encryption. -/
@[simp] lemma support_mgen_encrypt : (se_alg.mgen_encrypt m_dist).support =
  ⋃ m ∈ m_dist.support, ⋃ k ∈ (se_alg.keygen ()).support, {(m, se_alg.encrypt (m, k))} :=
by simp_rw [support_bind, support_return]

lemma mem_support_mgen_encrypt_iff (m : M) (c : C) :
  (m, c) ∈ (se_alg.mgen_encrypt m_dist).support ↔ m ∈ m_dist.support ∧
    ∃ k ∈ (se_alg.keygen ()).support, se_alg.encrypt (m, k) = c :=
by simp_rw [support_bind, support_return, set.mem_Union, set.mem_singleton_iff,
  prod.eq_iff_fst_eq_snd_eq, exists_and_distrib_left, exists_prop, exists_eq_left', @eq_comm _ c]

lemma exists_key_of_mem_support_mgen_encrypt (m : M) (c : C)
  (h : (m, c) ∈ (se_alg.mgen_encrypt m_dist).support) :
    ∃ k ∈ (se_alg.keygen ()).support, se_alg.encrypt (m, k) = c :=
((se_alg.mem_support_mgen_encrypt_iff m_dist m c).1 h).2

/-- The probability of getting a particular output `x` from `mgen_encrypt` is the sum over possible
keys such that encrypt `x.1` to `x.2`, of the probability of getting that key,
weighted by the probability of getting `x.1` from the message distribution. -/
lemma eval_dist_mgen_encrypt_apply (x : M × C) : ⁅= x | se_alg.mgen_encrypt m_dist⁆ =
  ∑' (k : K), if x.2 = se_alg.encrypt (x.1, k)
    then ⁅= x.1 | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ else 0 :=
begin
  simp only [←ennreal.tsum_mul_left, eval_dist_bind, eval_dist_bind_return, pmf.bind_apply,
    pmf.map_apply, mul_ite, mul_zero],
  refine trans (tsum_eq_single x.1 $ λ m hm, _) (tsum_congr $ λ k, _),
  { simp_rw [prod.eq_iff_fst_eq_snd_eq, hm.symm, false_and, if_false, tsum_zero] },
  { simp_rw [prod.eq_iff_fst_eq_snd_eq, eq_self_iff_true, true_and] }
end

lemma eval_dist_fst_map_mgen_encrypt : ⁅prod.fst <$> se_alg.mgen_encrypt m_dist⁆ = ⁅m_dist⁆ :=
by simp only [pmf.map_comp, eval_dist_map, eval_dist_bind, eval_dist_bind_return,
  pmf.map_bind, prod.fst_comp_mk, pmf.map_const, pmf.bind_pure]

end mgen_encrypt

section perfect_secrecy

/-- A symmetric encryption algorithm has perfect secrecy if the probability of any particular
ciphertext is the same, regardless of the plaintext. We express this as the fact that for any
distribution of messages `message_dist`, and fixed message `m` and ciphertext `c`,
the probability of getting `c` from encrypting a message drawn from `message_dist`
is the same as the probability of getting `c` from encrypting the fixed `m`. -/
def perfect_secrecy (se_alg : symm_enc_alg M K C) : Prop :=
∀ (m_dist : oracle_comp uniform_selecting M) (m : M) (c : C),
  indep_event (se_alg.mgen_encrypt m_dist) (prod.fst ⁻¹' {m}) (prod.snd ⁻¹' {c})

/-- Restate perfect secrecy in terms of explicit probabilities instead of indepent events.
A symmetric encryption algorithm has perfect secrecy iff the probability of getting a given
message-ciphertext after generating a key and encrypting is the probability of drawing the message
times the probability of getting that ciphertext from any message, for any message distribution. -/
theorem perfect_secrecy_iff : se_alg.perfect_secrecy ↔ ∀ (m_dist : oracle_comp uniform_selecting M)
  (m : M) (c : C), ⁅= (m, c) | se_alg.mgen_encrypt m_dist⁆ =
    ⁅= m | m_dist⁆ * ⁅= c | prod.snd <$> se_alg.mgen_encrypt m_dist⁆ :=
begin
  refine forall_congr (λ m_dist, (forall_congr (λ m, forall_congr (λ c, _)))),
  have this : prod.fst ⁻¹' {m} ∩ prod.snd ⁻¹' {c} = ({(m, c)} : set (M × C)),
  by {ext x, simp only [prod.eq_iff_fst_eq_snd_eq, set.mem_inter_iff,
    set.mem_preimage, set.mem_singleton_iff]},
  simp only [indep_event_iff, ← prob_event_map, prob_event_singleton_eq_eval_dist,
    eval_dist_fst_map_mgen_encrypt, this],
end

section equal_card

variables [fintype M] [fintype K] [fintype C]
  (hmk : fintype.card M = fintype.card K) (hkc : fintype.card K = fintype.card C)
include hmk hkc

/-- If all spaces have the same size we can get bijectivity of encrypt not just injectivity. -/
lemma encrypt_bijective_of_equal_card (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ m, se_alg.encrypt (m, k)).bijective :=
(fintype.bijective_iff_injective_and_card _).2
  ⟨se_alg.encrypt_injective k hk, hmk.trans hkc⟩

/-- If all spaces have the same size we can get bijectivity of decrypt not just surjectivity. -/
lemma decrypt_bijective_of_equal_card (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  (λ c, se_alg.decrypt (c, k)).bijective :=
(fintype.bijective_iff_surjective_and_card _).2
  ⟨se_alg.decrypt_surjective k hk, symm $ hmk.trans hkc⟩

/-- If all spaces are the same size then encryption and decryption are also left inverses. -/
lemma left_inverse_encrypt_decrypt : ∀ k ∈ (se_alg.keygen ()).support,
  function.left_inverse (λ m, se_alg.encrypt (m, k)) (λ c, se_alg.decrypt (c, k)) :=
λ k hk c, (se_alg.decrypt_bijective_of_equal_card hmk hkc k hk).1
  (by simp only [se_alg.complete _ k hk])

/-- Reverse version of completeness, i.e. encrypting a decryption gives the initial value. -/
lemma complete' (c : C) (k : K) (hk : k ∈ (se_alg.keygen ()).support) :
  se_alg.encrypt (se_alg.decrypt (c, k), k) = c :=
se_alg.left_inverse_encrypt_decrypt hmk hkc k hk c

section perfect_secrecy

/-- Given perfect secrecy and matching cardinatlities, every message-ciphertext pair must
give rise to a key that encrypts that message to that ciphertext. -/
theorem exists_unique_key_of_perfect_secrecy (h : se_alg.perfect_secrecy) (m : M) (c : C) :
  ∃! k, k ∈ (se_alg.keygen ()).support ∧ se_alg.encrypt (m, k) = c :=
begin
  have hmc : ∀ m c, ∃ k, k ∈ (se_alg.keygen ()).support ∧ se_alg.encrypt (m, k) = c,
  { intros m c,
    haveI : nonempty M := ⟨m⟩, -- Can't represent a uniform distribution on an empty type.
    suffices : 0 < ⁅= (m, c) | se_alg.mgen_encrypt ($ᵗ M)⁆,
    { rw [eval_dist_pos_iff_mem_support] at this,
      obtain ⟨k, hk, hk'⟩ := se_alg.exists_key_of_mem_support_mgen_encrypt ($ᵗ M) m c this,
      refine ⟨k, hk, hk'⟩ },
    {
      have this := (se_alg.perfect_secrecy_iff.1 h) ($ᵗ M) m c,
    simp_rw [this, ennreal.mul_pos_iff, eval_dist_pos_iff_mem_support,
      mem_support_uniform_select_fintype, mem_support_map_snd_iff, mem_support_mgen_encrypt_iff,
      mem_support_uniform_select_fintype M, true_and, exists_prop],
    obtain ⟨k, hk⟩ := (se_alg.keygen ()).support_nonempty,
    exact ⟨se_alg.decrypt (c, k), k, hk, se_alg.left_inverse_encrypt_decrypt hmk hkc k hk c⟩,
    }
  },
  have : (λ k, se_alg.encrypt (m, k)).bijective,
  {
    rw fintype.bijective_iff_surjective_and_card,
    refine ⟨λ c, _, hkc⟩,
    have := hmc m c,
    refine let ⟨k, _, hk⟩ := this in ⟨k, hk⟩,
  },

  refine exists_unique_of_exists_of_unique (hmc m c) _,

  refine λ k k' hk hk', _,
  have hkk' := hk.2.trans hk'.2.symm,
  refine this.1 hkk',
end

/-- Given perfect secrecy and matching cardinatlities, the keygen function must include
all possible keys in its set of possible outputs. -/
lemma support_keygen_of_perfect_secrecy (h : se_alg.perfect_secrecy) :
  (se_alg.keygen ()).support = set.univ :=
begin
  refine set.to_finset_eq_univ.1 (finset.eq_univ_of_card _ $ antisymm (finset.card_le_univ _) _),
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
  (λ k, se_alg.encrypt (m, k)).bijective :=
(function.bijective_iff_exists_unique _).2 $
  λ c, let ⟨k, hk, h'⟩ := se_alg.exists_unique_key_of_perfect_secrecy hmk hkc h m c
  in ⟨k, hk.2, λ k' hk', h' k' ⟨se_alg.mem_support_keygen hmk hkc h k', hk'⟩⟩

/-- If all spaces have the same size we can get bijectivity of encrypt not just injectivity,
where decryption is viewed as a function on keys with a fixed ciphertext. -/
lemma decrypt_key_bijective_of_perfect_secrecy (h : se_alg.perfect_secrecy) (c : C) :
  (λ k, se_alg.decrypt (c, k)).bijective :=
begin
  refine (function.bijective_iff_exists_unique _).2 (λ m, _),
  obtain ⟨k, hk, h'⟩ := se_alg.exists_unique_key_of_perfect_secrecy hmk hkc h m c,
  exact ⟨k, hk.2 ▸ se_alg.complete m k hk.1, λ k' hk', h' k' ⟨se_alg.mem_support_keygen
    hmk hkc h k', hk' ▸ se_alg.complete' hmk hkc c k' (se_alg.mem_support_keygen hmk hkc h k')⟩⟩,
end

lemma decrypt_encrypt_eq_iff_of_perfect_secrecy (h : se_alg.perfect_secrecy) (m : M) (k k' : K) :
  se_alg.decrypt (se_alg.encrypt (m, k), k') = m ↔ k = k' :=
have hk : k ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k),
have hk' : k' ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k'),
⟨λ h', (se_alg.encrypt_key_bijective_of_perfect_secrecy hmk hkc h m).1
  ((se_alg.decrypt_bijective_of_equal_card hmk hkc k' hk').1
  (h'.trans (se_alg.complete m k' hk').symm)), λ h', h' ▸ se_alg.complete m k hk⟩

lemma encrypt_decrypt_eq_iff_of_perfect_secrecy (h : se_alg.perfect_secrecy) (c : C) (k k' : K) :
  se_alg.encrypt (se_alg.decrypt (c, k), k') = c ↔ k = k' :=
have hk : k ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k),
have hk' : k' ∈ (se_alg.keygen ()).support := (se_alg.mem_support_keygen hmk hkc h k'),
⟨λ h', (se_alg.decrypt_key_bijective_of_perfect_secrecy hmk hkc h c).1
  ((se_alg.encrypt_bijective_of_equal_card hmk hkc k' hk').1
  (h'.trans (se_alg.complete' hmk hkc c k' hk').symm)), λ h', h' ▸ se_alg.complete' hmk hkc c k hk⟩

lemma eval_dist_key_eq_eval_dist_cipher_of_perfect_secrecy (h : se_alg.perfect_secrecy)
  (m_dist : oracle_comp uniform_selecting M) (k : K) (c : C)
  (h' : se_alg.decrypt (c, k) ∈ m_dist.support) :
  ⁅= k | se_alg.keygen ()⁆ = ⁅= c | prod.snd <$> se_alg.mgen_encrypt m_dist⁆ :=
begin
  let m := se_alg.decrypt (c, k),
  suffices : ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ =
    ⁅= m | m_dist⁆ * ⁅= c | prod.snd <$> se_alg.mgen_encrypt m_dist⁆,
  from (ennreal.mul_eq_mul_left (eval_dist_ne_zero_of_not_mem_support h') (pmf.apply_ne_top _ _)).1 this,
  calc ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ =
    ⁅= (m, k) | m_dist ×ₘ se_alg.keygen ()⁆ : by rw [eval_dist_product_apply]
    ... = ⁅= (m, c) | (λ (x : M × K), (x.1, se_alg.encrypt (x.1, x.2))) <$> (m_dist ×ₘ se_alg.keygen ())⁆ :
    begin
      refine symm (eval_dist_map_apply_eq_single' _ _ _ _ _ _),
      {
        simpa only [prod.mk.inj_iff, eq_self_iff_true, true_and] using
          se_alg.complete' hmk hkc c k (se_alg.mem_support_keygen hmk hkc h k),
      },
      {
        refine λ x hx hxm, _,
        simp only [prod.eq_iff_fst_eq_snd_eq] at hxm ⊢,
        refine ⟨hxm.1, _⟩,
        have : se_alg.encrypt (m, x.snd) = c := hxm.1 ▸ hxm.2,
        exact symm ((se_alg.encrypt_decrypt_eq_iff_of_perfect_secrecy hmk hkc h _ _ _).1 this),
      }
    end
    ... = ⁅= (m, c) | se_alg.mgen_encrypt m_dist⁆ :
      by simp_rw [product, eval_dist_map, eval_dist_bind,
        pmf.map_bind, eval_dist_return, pmf.map_pure]
    ... = ⁅= m | m_dist⁆ * ⁅= c | prod.snd <$> se_alg.mgen_encrypt m_dist⁆ :
      (se_alg.perfect_secrecy_iff.1 h) m_dist m c
end


/-- Assuming that the message, key, and ciphertext spaces all have the same size,
any system with perfect secrecy must generate keys uniformly at random. -/
theorem eval_dist_keygen_eq_uniform_of_perfect_secrecy [nonempty M] [nonempty C]
  (h : se_alg.perfect_secrecy) (k : K) :
  ⁅= k | se_alg.keygen ()⁆ = (fintype.card K)⁻¹ :=
calc ⁅= k | se_alg.keygen ()⁆ =
  1 * ⁅= k | se_alg.keygen ()⁆ : (one_mul _).symm
  ... = ((fintype.card C)⁻¹ * (fintype.card C)) * ⁅= k | se_alg.keygen ()⁆ :
    congr_arg (λ x, x * ⁅= k | se_alg.keygen ()⁆) ((ennreal.inv_mul_cancel (nat.cast_ne_zero.2
      fintype.card_ne_zero) $ by simp only [ne.def, ennreal.nat_ne_top, not_false_iff]).symm)
  ... = (fintype.card C)⁻¹ * (∑' (c : C), ⁅= k | se_alg.keygen ()⁆) :
    by simp only [tsum_fintype, finset.sum_const, fintype.card, ←mul_assoc, nsmul_eq_mul]
  ... = (fintype.card C)⁻¹ * (∑' (c : C), ⁅= c | prod.snd <$> se_alg.mgen_encrypt ($ᵗ M)⁆) :
    congr_arg (λ x, (fintype.card C)⁻¹ * x) (tsum_congr $ λ c,
      se_alg.eval_dist_key_eq_eval_dist_cipher_of_perfect_secrecy hmk hkc h _ k c
        (mem_support_uniform_select_fintype _ _))
  ... = (fintype.card C)⁻¹ : by rw [pmf.tsum_coe, mul_one]
  ... = (fintype.card K)⁻¹ : by rw hkc

/-- Given that all spaces have the same cardinality, perfect secrecy holds iff:
1. `keygen` chooses keys uniformly at random.
2. for every message `m` and ciphertext `c`, there is a unique key encrypting `m` to `c`.
In particular this will be used to show perfect secrecy of the one-time pad.-/
theorem perfect_secrecy_iff_of_equal_card [nonempty M] [nonempty C] :
  se_alg.perfect_secrecy ↔
  (∀ k, ⁅= k | se_alg.keygen ()⁆ = (fintype.card K)⁻¹) ∧
    (∀ m c, ∃! k, k ∈ (se_alg.keygen ()).support ∧ se_alg.encrypt (m, k) = c) :=
begin
  split,
  { refine λ h, ⟨se_alg.eval_dist_keygen_eq_uniform_of_perfect_secrecy hmk hkc h,
      λ m c, se_alg.exists_unique_key_of_perfect_secrecy hmk hkc h m c⟩ },
  { rw [perfect_secrecy_iff],
    rintros ⟨h_keygen, h_encrypt⟩ m_dist m c,
    obtain ⟨k, ⟨⟨hkₛ, rfl⟩, hk⟩⟩ := h_encrypt m c,
    calc ⁅= (m, se_alg.encrypt (m, k)) | se_alg.mgen_encrypt m_dist⁆ =
      ∑' k', if se_alg.encrypt (m, k) = se_alg.encrypt (m, k')
        then ⁅= m | m_dist⁆ * ⁅= k' | se_alg.keygen ()⁆ else 0 : by rw eval_dist_mgen_encrypt_apply
      ... = ∑' k', if k = k' then ⁅= m | m_dist⁆ * ⁅= k' | se_alg.keygen ()⁆ else 0 :
        begin
          refine tsum_congr (λ k', symm _),
          by_cases hk0 : k' ∈ (se_alg.keygen ()).support,
          { exact ite_eq_iff'.2 ⟨λ hk'', by rw [hk'', eq_self_iff_true, if_true], λ hkn, symm $
              ite_eq_right_iff.2 $ λ hk'', false.elim (hkn (hk k' ⟨hk0, hk''.symm⟩).symm)⟩ },
          { simp_rw [(eval_dist_eq_zero_iff_not_mem_support _ _).2 hk0, mul_zero, if_t_t] }
        end
      ... = if k = k then ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ else 0 :
        tsum_eq_single k (λ k' hk', by simp_rw [hk'.symm, if_false])
      ... = ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ : if_pos rfl
      ... = ⁅= m | m_dist⁆ * ∑' m', ⁅= m' | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ :
        by rw [ennreal.tsum_mul_right, ⁅m_dist⁆.tsum_coe, one_mul]
      ... = ⁅= m | m_dist⁆ * ∑' m', ⁅= (m', se_alg.encrypt (m, k)) | se_alg.mgen_encrypt m_dist⁆ :
        begin
          refine congr_arg (λ x, _ * x) (tsum_congr (λ m', symm _)),
          simp_rw [eval_dist_mgen_encrypt_apply],
          obtain ⟨k', hks', hke'⟩ := h_encrypt m' (se_alg.encrypt (m, k)),
          refine trans (tsum_eq_single k' $ λ kd hkd, _) _,
          { by_cases hkds : kd ∈ (se_alg.keygen ()).support,
            { exact ite_eq_right_iff.2 (λ hkkd, false.elim (hkd $ hke' kd ⟨hkds, hkkd.symm⟩)) },
            { simp_rw [(eval_dist_eq_zero_iff_not_mem_support _ _).2 hkds, mul_zero, if_t_t] } },
          { simp_rw [hks'.2, eq_self_iff_true, if_true, h_keygen] }
        end
      ... = ⁅= m | m_dist⁆ * ⁅= se_alg.encrypt (m, k) | prod.snd <$> se_alg.mgen_encrypt m_dist⁆ :
        begin
          refine congr_arg (λ x, _ * x) _,
          rw [eval_dist_map_apply_eq_tsum, ennreal.tsum_prod'],
          refine tsum_congr (λ m', symm $ trans (tsum_eq_single
            (se_alg.encrypt (m, k)) $ λ c hc, if_neg hc.symm) (if_pos rfl)),
        end
  }
end

end perfect_secrecy

end equal_card

end perfect_secrecy

end symm_enc_alg