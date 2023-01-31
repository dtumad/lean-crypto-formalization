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

/-- A symmetric-key encryption algorithm is a set of functions `gen`, `encrypt`, and `decrypt`.
The types `M`, `K`, and `C` are the types of the messages, keys, and ciphertexts respectively.
`spec` gives the oracles given to the algorithms, usually `coin_oracle` or `uniform_selecting`. -/
structure symm_enc_alg :=
(M K C : Type)
(spec : oracle_spec)
(keygen : unit → oracle_comp spec K)
(encrypt : M × K → oracle_comp spec C)
(decrypt : C × K → oracle_comp spec M)
-- (keygen_poly_time : poly_time_oracle_comp keygen)
-- (encrypt_poly_time : poly_time_oracle_comp encrypt)
-- (decrypt_poly_time : poly_time_oracle_comp decrypt)

namespace symm_enc_alg

section complete

/-- A symmetric encryption algorithm is complete if encrypt and decrypt are -/
def complete (se_alg : symm_enc_alg) : Prop :=
∀ (m : se_alg.M), ⁅(=) m | do {
  k ← se_alg.keygen (),
  c ← se_alg.encrypt (m, k),
  m' ← se_alg.decrypt (c, k),
  return m'
}⁆ = 1

variable (se_alg : symm_enc_alg)

lemma complete_iff : se_alg.complete ↔
  ∀ (m : se_alg.M), ∀ k ∈ (se_alg.keygen ()).support,
    ∀ c ∈ (se_alg.encrypt (m, k)).support,
    (se_alg.decrypt (c, k)).support ⊆ {m} :=
begin
  simp_rw [complete, prob_event_eq_eq_eval_dist],
  simp_rw [eval_dist_eq_one_iff_support_subset_singleton],
  simp,

end

end complete

end symm_enc_alg