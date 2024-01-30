/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.zip
import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.fork.fork
import crypto_constructions.hhs_signatures.commits

/-!
# Signature Scheme Based On Hard Homogenous Spaces

This file defines a signature scheme based on hard homogenous spaces,
using a generalized version of the basic Schnorr signature scheme.

We prove both completeness and unforgeability, providing an explicit reduction
from signature forgery to a vectorization forgery.
-/

open_locale ennreal big_operators
open oracle_comp oracle_spec prod vector

/-- Schnorr signature derived from a hard homogenous space, based on the diffie helmann case.
`X` is the space of base points in the HHS, and `G` is the space of vectors between them.
`n` represents the number of commitments to make, more corresponding to more difficult forgery.
Public keys are pairs `(x₀, pk)` of a base point and a key point.
The secret key is the vectorization between the points `x₀` and `pk`, as an element of `G`.
We use a random oracle `(vector X n × M) ↦ₒ vector bool n` to hash the commitment values. -/
noncomputable def hhs_signature (G X M : Type) [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] (n : ℕ) :
  signature_alg (unif_spec ++ ((vector X n × M) ↦ₒ vector bool n))
    M (X × X) G (vector G n × vector bool n) :=
{ keygen := λ u, do {x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk)},
  -- Sign a message by choosing `n` random commitments, and querying the oracle on them
  -- For each 1 bit in the resulting hash, subtract the secret key from corresponding commitment
  sign := λ ⟨⟨⟨x₀, pk⟩, sk⟩, m⟩, do
  { gs : vector G n ←$ᵗ (vector G n),
    xs : vector X n ← return (gs.map (+ᵥ pk)),
    hash : vector bool n ← query (sum.inr ()) (xs, m),
    return (zip_commits sk gs hash, hash) },
  -- Verify a signature by adding each commit to the appropriate point in the public key
  -- Signatures are valid if the result of hashing this matches the original hash
  verify := λ ⟨⟨x₀, pk⟩, m, zs, hash⟩, do
  { (xs : vector X n) ← return (unzip_commits x₀ pk zs hash),
    (hash' : vector bool n) ← query (sum.inr ()) (xs, m),
    return (hash' = hash) },
  -- Treat the second oracle as a random oracle
  base_oracle := (idₛₒ ++ₛ randomₛₒ).mask_state (equiv.punit_prod _),
  init_state := ∅, .. }

namespace hhs_signature

variables {G X M : Type} [decidable_eq M] [add_comm_group G]
  [algorithmic_homogenous_space G X] {n : ℕ}

lemma base_oracle_eq : (hhs_signature G X M n).base_oracle =
  (idₛₒ ++ₛ randomₛₒ).mask_state (equiv.punit_prod _) := rfl

@[simp] lemma base_S_eq : (hhs_signature G X M n).base_S =
  query_log ((vector X n × M) ↦ₒ vector bool n) := rfl

@[simp] lemma init_state_eq : (hhs_signature G X M n).init_state = (∅ : query_log _) := rfl

section keygen

variables (u : unit)

lemma keygen_apply : (hhs_signature G X M n).keygen u =
  do {x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk)} := rfl

@[simp] lemma simulate_keygen_apply (cache : query_log ((vector X n × M) ↦ₒ vector bool n)) :
  simulate ((hhs_signature G X M n).base_oracle) ((hhs_signature G X M n).keygen u) cache =
    do {x₀ ←$ᵗ X, sk ←$ᵗ G, return (((x₀, sk +ᵥ x₀), sk), cache)} :=
by simp [keygen_apply, bind_assoc, base_oracle_eq,
  equiv.punit_prod_symm_apply ((vector X n × M ↦ₒ vector bool n).query_log)]

@[simp] lemma simulate'_keygen_apply (cache : query_log ((vector X n × M) ↦ₒ vector bool n)) :
  simulate' (hhs_signature G X M n).base_oracle ((hhs_signature G X M n).keygen u) cache =
    do {x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk)} :=
by simp_rw [simulate'.def, simulate_keygen_apply, map_bind, map_return]

end keygen

-- TODO: in the next few section it might be good to collapse input variables

section sign

variables (x₀ pk : X) (sk : G) (m : M)

lemma sign_apply : ((hhs_signature G X M n).sign (((x₀, pk), sk), m)) =
  do {gs ←$ᵗ (vector G n), hash ← query (sum.inr ()) (gs.map (+ᵥ pk), m),
    return (zip_commits sk gs hash, hash)} := rfl

@[simp] lemma simulate_sign_apply (cache : query_log ((vector X n × M) ↦ₒ vector bool n)) :
  simulate (hhs_signature G X M n).base_oracle
    ((hhs_signature G X M n).sign (((x₀, pk), sk), m)) cache =
  do {gs ←$ᵗ (vector G n), hash' ← return (cache.lookup () (gs.map (+ᵥ pk), m)),
    option.rec_on hash' ($ᵗ (vector bool n) >>= λ hash,
      return ((zip_commits sk gs hash, hash), cache.log_query () (gs.map (+ᵥ pk), m) hash))
    (λ hash, return ((zip_commits sk gs hash, hash), cache)) } 
    :=
begin
  simp [sign_apply, bind_assoc, random_oracle.def, base_oracle_eq,
    equiv.punit_prod_symm_apply ((vector X n × M ↦ₒ vector bool n).query_log)],
  refine bind_ext_congr (λ gs, _),
  cases cache.lookup () (map (λ g, g +ᵥ pk) gs, m),
  { simpa [bind_assoc] },
  { simp [bind_assoc] }
end

@[simp] lemma simulate'_sign_apply (cache : query_log ((vector X n × M) ↦ₒ vector bool n)) :
  simulate' (hhs_signature G X M n).base_oracle
    ((hhs_signature G X M n).sign (((x₀, pk), sk), m)) cache =
  do {gs ←$ᵗ (vector G n), hash' ← return (cache.lookup () (gs.map (+ᵥ pk), m)),
    option.rec_on hash' ((λ hash, (zip_commits sk gs hash, hash)) <$> $ᵗ (vector bool n))
      (λ hash, return (zip_commits sk gs hash, hash)) } :=
begin
  simp [simulate'.def],
  refine bind_ext_congr (λ gs, _),
  cases cache.lookup () (map (λ g, g +ᵥ pk) gs, m); simp [bind_assoc]
end

end sign

section verify 

variables (x₀ pk : X) (m : M) (zs : vector G n) (hash : vector bool n)

lemma verify_apply : ((hhs_signature G X M n).verify ((x₀, pk), m, zs, hash)) =
  do {hash' ← query (sum.inr ()) (unzip_commits x₀ pk zs hash, m),
    return (hash' = hash)} := rfl

@[simp] lemma simulate_verify_apply (cache : query_log ((vector X n × M) ↦ₒ vector bool n)) :
  simulate (hhs_signature G X M n).base_oracle
    ((hhs_signature G X M n).verify ((x₀, pk), m, zs, hash)) cache =
  let xs := unzip_commits x₀ pk zs hash in
  do {maybe_hash ← return (cache.lookup () (xs, m)), option.rec_on maybe_hash
    (do {hash' ←$ᵗ (vector bool n), return (hash' = hash, cache.log_query () (xs, m) hash')})
    (λ hash', return (hash' = hash, cache))} :=
begin
  simp [verify_apply, bind_assoc, random_oracle.def, base_oracle_eq,
    equiv.punit_prod_symm_apply ((vector X n × M ↦ₒ vector bool n).query_log)],
  cases cache.lookup () (unzip_commits x₀ pk zs hash, m),
  { simpa [bind_assoc] },
  { simp }
end

@[simp] lemma simulate_verify_apply_empty : simulate (hhs_signature G X M n).base_oracle
    ((hhs_signature G X M n).verify ((x₀, pk), m, zs, hash)) (indexed_list.empty _ _) =
  do {hash' ←$ᵗ (vector bool n), return (hash' = hash,
    query_log.log_query (indexed_list.empty _ _) () (unzip_commits x₀ pk zs hash, m) hash')} :=
simulate_verify_apply x₀ pk m zs hash (indexed_list.empty _ _)

@[simp] lemma simulate'_verify_apply (cache : query_log ((vector X n × M) ↦ₒ vector bool n)) :
  simulate' (hhs_signature G X M n).base_oracle
    ((hhs_signature G X M n).verify ((x₀, pk), m, zs, hash)) cache =
  let xs := unzip_commits x₀ pk zs hash in
  do {maybe_hash ← return (cache.lookup () (xs, m)), option.rec_on maybe_hash
    (do {hash' ←$ᵗ (vector bool n), return (hash' = hash)})
    (λ hash', return (hash' = hash))} :=
begin
  simp [verify_apply, bind_assoc, random_oracle.def, base_oracle_eq,
    equiv.punit_prod_symm_apply ((vector X n × M ↦ₒ vector bool n).query_log)],
  cases cache.lookup () (unzip_commits x₀ pk zs hash, m),
  { simpa [bind_assoc] },
  { simp }
end

end verify

theorem is_sound : (hhs_signature G X M n).is_sound :=
begin
  simp only [signature_alg.is_sound, signature_alg.soundness_exp.advantage_eq,
    oracle_algorithm.exec_bind, simulate_keygen_apply, bind_assoc, oracle_comp.return_bind,
    simulate'_bind, init_state_eq, simulate_sign_apply, bind_assoc, query_log.lookup_empty,
    oracle_comp.return_bind, bind_assoc],
  refine λ m, prob_output_bind_of_const _ _ (λ x₀ _, _),
  refine prob_output_bind_of_const _ _ (λ sk _, _),
  refine prob_output_bind_of_const _ _ (λ gs _, _),
  simp only [simulate'_verify_apply, unzip_commits_zip_commits, vadd_vadd, if_t_t, zip_with_const],
  refine prob_output_bind_of_const _ _ (λ hash _, _),
  refine prob_output_bind_of_const _ _ (λ maybe_hash h2, _),
  have : maybe_hash = some hash,
  from trans h2 (by simp only [query_log.lookup, query_log.log_query_apply,
    eq_self_iff_true, if_true, dite_eq_ite, indexed_list.empty_apply, list.nil_append,
    list.find, function.comp, option.map_eq_map, option.map_some']),
  rw [this], simp
end

end hhs_signature