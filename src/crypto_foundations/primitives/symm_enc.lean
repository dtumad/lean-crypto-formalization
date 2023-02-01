/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad
import computational_monads.asymptotics.polynomial_time

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.
-/

open oracle_spec oracle_comp
open_locale classical

/-- A symmetric-key encryption algorithm is a set of functions `gen`, `encrypt`, and `decrypt`.
The types `M`, `K`, and `C` are the types of the messages, keys, and ciphertexts respectively.
`spec` gives the oracles given to the algorithm, usually `coin_oracle` or `uniform_selecting`. -/
structure symm_enc_alg (M K C : Type) :=
(spec : oracle_spec)
(keygen : unit → oracle_comp spec K)
(encrypt : M × K → C)
(decrypt : C × K → M)
-- (keygen_poly_time : poly_time_oracle_comp keygen)
-- (encrypt_poly_time : poly_time_oracle_comp encrypt)
-- (decrypt_poly_time : poly_time_oracle_comp decrypt)

namespace symm_enc_alg

variables {M K C : Type} (se_alg : symm_enc_alg M K C)

lemma eval_dist_keygen_encrypt_apply' (m : M) (c : C) :
  ⁅= c | do {k ← se_alg.keygen (), return (se_alg.encrypt (m, k))}⁆ =
    ∑' (k : K), if c = se_alg.encrypt (m, k) then ⁅= k | se_alg.keygen ()⁆ else 0 :=
by rw [eval_dist_bind_return_apply_eq_tsum]

lemma eval_dist_keygen_encrypt_apply (m_dist : oracle_comp se_alg.spec M) (c : C) :
  ⁅= c | do {m ← m_dist, k ← se_alg.keygen (), return (se_alg.encrypt (m, k))}⁆ =
    ∑' (m : M) (k : K), if c = se_alg.encrypt (m, k)
      then ⁅= m | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ else 0 :=
by simp_rw [eval_dist_bind_apply_eq_tsum, eval_dist_return_apply,
  ← ennreal.tsum_mul_left,  mul_ite, mul_one, mul_zero]

section complete

/-- A symmetric encryption algorithm is complete if encrypt and decrypt are -/
def complete (se_alg : symm_enc_alg M K C) : Prop :=
∀ (m : M), ⁅= m | do {
  k ← se_alg.keygen (),
  return $ se_alg.decrypt (se_alg.encrypt (m, k), k)
}⁆ = 1

lemma complete_iff : se_alg.complete ↔ ∀ (m : M), ∀ k ∈ (se_alg.keygen ()).support,
  (se_alg.decrypt (se_alg.encrypt (m, k), k)) = m :=
by simp_rw [complete, eval_dist_eq_one_iff_support_subset_singleton, support_bind, support_return,
  set.Union_subset_iff, set.subset_singleton_iff, set.mem_singleton_iff, forall_eq]

end complete

section perfect_secrecy

/-- A symmetric encryption algorithm has perfect secrecy if the probability of any particular
ciphertext is the same, regardless of the plaintext. We express this as the fact that for any
distribution of messages `message_dist`, and fixed message `m` and ciphertext `c`,
the probability of getting `c` from encrypting a message drawn from `message_dist`
is the same as the probability of getting `c` from encrypting the fixed `m`. -/
def perfect_secrecy (se_alg : symm_enc_alg M K C) : Prop :=
∀ (m_dist : oracle_comp se_alg.spec M) (m : M) (c : C),
  ⁅= c | do {m' ← m_dist, k ← se_alg.keygen(), return $ se_alg.encrypt (m', k)}⁆ =
    ⁅= c | do {k ← se_alg.keygen (), return $ se_alg.encrypt (m, k)}⁆

/-- Rewrite perfect secrecy in terms of distributions rather than specific probabilities. -/
lemma perfect_secrecy_iff_eval_dist_eq_eval_dist : se_alg.perfect_secrecy ↔
  ∀ (m_dist : oracle_comp se_alg.spec M) (m : M),
    ⁅do {m' ← m_dist, k ← se_alg.keygen (), return $ se_alg.encrypt (m', k)}⁆ =
      ⁅do {k ← se_alg.keygen (), return $ se_alg.encrypt (m, k)}⁆ :=
by simp_rw [perfect_secrecy, eval_dist.ext_iff]

/-- Rewrite perfect secrecy in terms of probability summations rather than probabilities. -/
lemma perfect_secrecy_iff_tsum_eq_tsum : se_alg.perfect_secrecy ↔
  ∀ (m_dist : oracle_comp se_alg.spec M) (m : M) (c : C),
    (∑' (m' : M) (k : K), if c = se_alg.encrypt (m', k)
      then ⁅= m' | m_dist⁆ * ⁅= k | se_alg.keygen ()⁆ else 0) =
    (∑' (k : K), if c = se_alg.encrypt (m, k)
      then ⁅= k | se_alg.keygen ()⁆ else 0) :=
by simp_rw [perfect_secrecy, eval_dist_keygen_encrypt_apply', eval_dist_keygen_encrypt_apply]

/-- If a symmetric encryption scheme has perfect secrecy then th distribution of
ciphertexts is independent of whatever message is being encrypted. -/
lemma eval_dist_apply_eq_eval_dist_apply_of_perfect_secrecy' (h : se_alg.perfect_secrecy)
  (m m' : M) : ⁅do {k ← se_alg.keygen (), return $ se_alg.encrypt (m, k)}⁆ =
    ⁅do {k ← se_alg.keygen (), return $ se_alg.encrypt (m', k)}⁆ :=
begin
  rw [perfect_secrecy_iff_eval_dist_eq_eval_dist] at h,
  exact trans (h (return m) m).symm (h (return m) m'),
end

end perfect_secrecy

end symm_enc_alg