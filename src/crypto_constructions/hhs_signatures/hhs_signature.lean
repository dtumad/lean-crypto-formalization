/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.zip

import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.repeat_n
import computational_monads.constructions.forking_lemma

open oracle_comp oracle_spec

section commits

variables {G X M : Type} [fintype G] [fintype X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

/-- Function used in signing to combine the random commitments with the resulting hash,
  using the provided secret key to prove that the secret key corresponds to the public key -/
@[reducible, inline]
def zip_commits_with_hash (cs : vector G n) (h : vector bool n) (sk : G) : vector (G × bool) n :=
vector.zip_with (λ c (b : bool), (if b then c else c + sk, b)) cs h

lemma zip_commits_with_hash_nil (sk : G) :
  zip_commits_with_hash vector.nil vector.nil sk = vector.nil :=
rfl

@[reducible, inline]
def retrieve_commits (x₀ pk: X) (σ : vector (G × bool) n) : vector X n :=
(σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀))

lemma retrieve_commits_nil (x₀ pk : X) :
  retrieve_commits x₀ pk (@vector.nil $ G × bool) = vector.nil :=
rfl

end commits

/-- Signature derived from a hard homogenous space, based on the diffie helmann case.
  `n` represents the number of commitments to make, more corresponding to more difficult forgery.
  `x₀` is some arbitrary public base point in `X`, used to compute public keys from secret keys -/
noncomputable def hhs_signature (G X M : Type) (n : ℕ) [fintype G] [fintype X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M] [add_group G]
  [algorithmic_homogenous_space G X] : signature :=
{ M := M, PK := X × X, SK := G, S := vector (G × bool) n,
  gen := λ _, do {
    x₀ ←$ᵗ X,
    sk ←$ᵗ G,
    return ((x₀, sk +ᵥ x₀), sk)
  },
  sign := λ ⟨⟨x₀, pk⟩, sk, m⟩, do {
    (cs : vector G n) ← repeat_n ($ᵗ G) n,
    (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
    (h : vector bool n) ← query₂ () (ys, m),
    return (zip_commits_with_hash cs h sk)
  },
  verify := λ ⟨⟨x₀, pk⟩, m, σ⟩, do {
    (h : vector bool n) ← query₂ () (retrieve_commits x₀ pk σ, m),
    return (h = σ.map prod.snd) 
  },
  random_oracle_spec := ((vector X n × M) ↦ₒ vector bool n),
  random_oracle_spec_finite_range := singleton_spec.finite_range _ _,
  random_oracle_spec_computable := singleton_spec.computable _ _,
  decidable_eq_M := by apply_instance,
  decidable_eq_S := by apply_instance,
  inhabited_S := by apply_instance }

namespace hhs_signature 

variables {G X M : Type} [fintype G] [fintype X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

@[simp]
lemma support_coe_uniform_selecting_oracles [inhabited G] {α : Type}
  (oa : oracle_comp uniform_selecting α) :
  support (↑oa : oracle_comp (hhs_signature G X M n).base_oracle_spec α) = oa.support :=
begin
  sorry
end

section gen

@[simp]
lemma gen_apply (u : unit) :
  ((hhs_signature G X M n).gen u) = do { x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk) } :=
rfl

lemma support_gen : ((hhs_signature G X M n).gen ()).support =
  ⋃ (x₀ : X) (sk : G), { ((x₀, sk +ᵥ x₀), sk) } :=
by simp only [gen_apply, support_bind_bind, support_coe_uniform_selecting_oracles,
  support_uniform_select_fintype, support_return, set.Union_true]

end gen

section sign

@[simp]
lemma sign_apply (x₀ pk : X) (sk : G) (m : M) :
  ((hhs_signature G X M n).sign ((x₀, pk), sk, m)) = do {
    (cs : vector G n) ← repeat_n ($ᵗ G) n,
    (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
    (h : vector bool n) ← query₂ () (ys, m),
    return (zip_commits_with_hash cs h sk)
  } :=
rfl

@[simp]
lemma support_sign (x₀ pk : X) (sk : G) (m : M) :
  ((hhs_signature G X M n).sign ((x₀, pk), sk, m)).support =
    ⋃ (cs : vector G n) (h : vector bool n), { zip_commits_with_hash cs h sk } :=
sorry

end sign

section verify

@[simp]
lemma verify_apply {n : ℕ} (x₀ pk : X) (m : M) (σ : vector (G × bool) n) :
  ((hhs_signature G X M n).verify ((x₀, pk), m, σ)) = do {
    (h : vector bool n) ← query₂ () (retrieve_commits x₀ pk σ, m),
    return (h = σ.map prod.snd) 
  } :=
rfl

end verify

section complete

theorem hhs_signature_complete [inhabited G] :
  (hhs_signature G X M n).complete :=
begin
  rw signature.complete_iff_signatures_support_subset,
  rintros m ⟨x₀, pk⟩ sk σ hgen hsign,
  sorry
end

end complete

section mock_signing_oracle

-- set_option trace.class_instances true

/-- Oracle to mock a signing oracle for messages in the vectorization reduction.
Predetermines the random oracle results to fake a valid signature,
keeping the results in a seperate internal mocked cache.
Queries to the random oracle are first filtered through this,
and are passed to the true random oracle only if the query is fresh. -/
noncomputable def mock_signing_oracle (x₀ pk : X) :
  sim_oracle (hhs_signature G X M n).unforgeable_adversary_oracle_spec
    (hhs_signature G X M n).base_oracle_spec
    (query_log (hhs_signature G X M n).random_oracle_spec) :=
{ default_state := query_log.init _,
  o := λ i, match i with
  -- For uniform selection queries, simply forward them to the lower level.
  | (sum.inl (sum.inl i)) := λ ⟨t, mock_cache⟩, do {
    u ← query (sum.inl i) t,
    return (u, mock_cache)
  }
  -- For random oracle queries, check if the query has been mocked.
  -- If so, return the mocked value, otherwise call the regular random oracle
  | (sum.inl (sum.inr i)) := λ ⟨t, mock_cache⟩, mock_cache.lookup_cached_or_run i t
    (@query (hhs_signature G X M n).base_oracle_spec (sum.inr i) t)
  | (sum.inr ()) := λ ⟨m, mock_cache⟩, do {
    bs ← repeat_n ($ᵗ bool) n, -- pre-select what all the bool results will be.
    cs ← repeat_n ($ᵗ G) n,
    ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
    mock_cache' ← return (mock_cache.log_query () (ys, m) bs),
    return (vector.zip_with prod.mk cs bs, mock_cache')
  }
  end }

end mock_signing_oracle

section mock_signing_reduction

noncomputable def mock_signing_reduction (adv : (hhs_signature G X M n).unforgeable_adversary)
  (x₀ pk : X) : oracle_comp (hhs_signature G X M n).base_oracle_spec (M × vector (G × bool) n) :=
do {
  ⟨m, σ⟩ ← default_simulate' (mock_signing_oracle x₀ pk) (adv.adv (x₀, pk)),
  _ ← query₂ () (retrieve_commits x₀ pk σ, m), -- force a query to the final output
  return (m, σ)
}

end mock_signing_reduction

section choose_fork

/- The choose_fork that will be passed to forking lemma. `q` will be the
max queries of the adversary (given by `polynomial_queries` assumption).
Returns none if it hasn't been queried or if the signature isn't valid -/
noncomputable def choose_fork (x₀ pk : X) (m : M) (σ : vector (G × bool) n)
  (log : query_log (hhs_signature G X M n).random_oracle_spec) (q : ℕ) : option (fin q) :=
match log.lookup_with_index () (retrieve_commits x₀ pk σ, m) with
| none := none
| (some ⟨h, index⟩) := if hq : index < q ∧ h = σ.map prod.snd then some ⟨index, hq.1⟩ else none
end

end choose_fork

section fork_reduction

/-- Reduce an unforgeability adversery to a forking adversary that can be passed to
`oracle_comp.fork` to get two results, that can be used to construct a adversary for
vectorization in the hard homogenous space.
`q` is the maximum number of queries made by the adversary to consider. -/
noncomputable def forking_adversary_reduction (adv : (hhs_signature G X M n).unforgeable_adversary)
  (x₀ pk : X) (q : ℕ) :
  forking_adversary (vector X n × M) (vector bool n)
    ((M × vector (G × bool) n)) :=
{ adv := mock_signing_reduction adv x₀ pk,
  q := q,
  choose_fork := λ ⟨m, σ⟩ log, choose_fork x₀ pk m σ log q,
  cache_nonempty := sorry,
  no_overflow := sorry,
}

end fork_reduction

section vectorization_reduction

def vectorization_of_signatures (σ σ' : list (G × bool)) : G :=
(σ.zip σ').foldr (λ ⟨⟨g₀, b⟩, ⟨g₁, b'⟩⟩ g, if b = b' then g₀ - g₁ else g) (arbitrary G)

/-- Reduce an unforgeability adversery to a hhs vectorization adversary,
by forking the adversary and using the two different results -/
noncomputable def vectorization_adversary_reduction [inhabited G]
  (adversary : signature.unforgeable_adversary $ hhs_signature G X M n)
  (q : ℕ) : vectorization.adversary G X :=
{ adv := λ ⟨pk, x₀⟩, do {
    ⟨i, ⟨m, σ⟩, cache, ⟨m', σ'⟩, cache'⟩ ← fork (forking_adversary_reduction adversary pk x₀ q),
    return (vectorization_of_signatures σ.to_list σ'.to_list)
  } }

end vectorization_reduction

end hhs_signature


/-- Construct a signature scheme by incrementing both the hard homogenous space parameter,
and the number of commits made by the signature.
Both are controlled by the same parameter, but this could eventually be generalized -/
noncomputable def hhs_signature_scheme (G X : ℕ → Type) (M : Type)
  [∀ n, fintype $ G n] [∀ n, fintype $ X n] [∀ n, inhabited $ G n]
  [∀ n, decidable_eq $ G n] [∀ n, decidable_eq $ X n] [decidable_eq M]
  [∀ n, add_group $ G n] [∀ n, algorithmic_homogenous_space (G n) (X n)]
  [hard_homogenous_space G X] : signature_scheme :=
λ n, hhs_signature (G n) (X n) M n

namespace hhs_signature_scheme

section unforgeable

variables (G X : ℕ → Type) (M : Type)
  [∀ n, fintype $ G n] [∀ n, fintype $ X n] [∀ n, inhabited $ G n]
  [∀ n, decidable_eq $ G n] [∀ n, decidable_eq $ X n] [decidable_eq M]
  [∀ n, add_group $ G n] [∀ n, algorithmic_homogenous_space (G n) (X n)]
  [hard_homogenous_space G X]

theorem hhs_signature_scheme_unforgeable : (hhs_signature_scheme G X M).unforgeable :=
begin
  rintros adversary ⟨p, hp⟩,
  let reduction : Π (sp : ℕ), vectorization.adversary (G sp) (X sp) :=
    λ n, hhs_signature.vectorization_adversary_reduction (adversary n) (p.eval n),
  have := hard_homogenous_space.vectorization_hard reduction,
  sorry,
end

end unforgeable

end hhs_signature_scheme