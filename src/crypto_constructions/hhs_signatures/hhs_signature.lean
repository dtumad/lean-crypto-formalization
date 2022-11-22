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

/-!
# Signature Scheme Based On Hard Homogenous Spaces

This file defines a signature scheme based on hard homogenous spaces,
using a generalized version of the basic Diffie-Helmann signature scheme.

We prove both completeness and unforgeability, providing an explicit reduction
from signature forgery to a vectorization forgery.
-/

noncomputable theory

open oracle_comp oracle_spec

section commits

variables {G X M : Type} [fintype G] [fintype X] [inhabited G] [inhabited X]
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
def hhs_signature (G X M : Type) (n : ℕ) [fintype G] [fintype X] [inhabited G] [inhabited X]
  [decidable_eq G] [decidable_eq X] [decidable_eq M] [add_group G]
  [algorithmic_homogenous_space G X] : signature :=
{ M := M, PK := X × X, SK := G, S := vector (G × bool) n,
  gen := λ _,
  do{ x₀ ←$ᵗ X, sk ←$ᵗ G,
      return ((x₀, sk +ᵥ x₀), sk) },
  sign := λ ⟨⟨x₀, pk⟩, sk, m⟩,
  do{ (cs : vector G n) ← repeat_n ($ᵗ G) n,
      (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
      (h : vector bool n) ← query₂ () (ys, m),
      return (zip_commits_with_hash cs h sk) },
  verify := λ ⟨⟨x₀, pk⟩, m, σ⟩,
  do{ (h : vector bool n) ← query₂ () (retrieve_commits x₀ pk σ, m),
      return (h = σ.map prod.snd) },
  random_oracle_spec := ((vector X n × M) ↦ₒ vector bool n),
  random_oracle_spec_finite_range := singleton_spec.finite_range _ _,
  random_oracle_spec_computable := singleton_spec.computable _ _,
  decidable_eq_M := by apply_instance,
  decidable_eq_S := by apply_instance,
  inhabited_S := by apply_instance }

namespace hhs_signature 

variables {G X M : Type} [fintype G] [fintype X] [inhabited G] [inhabited X]
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
lemma gen_apply (u : unit) : ((hhs_signature G X M n).gen u) =
  do { x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk) } := rfl

lemma support_gen : ((hhs_signature G X M n).gen ()).support =
  ⋃ (x₀ : X) (sk : G), { ((x₀, sk +ᵥ x₀), sk) } :=
by simp only [gen_apply, support_bind_bind, support_coe_uniform_selecting_oracles,
  support_uniform_select_fintype, support_return, set.Union_true]

end gen

section sign

@[simp]
lemma sign_apply (x₀ pk : X) (sk : G) (m : M) :
  ((hhs_signature G X M n).sign ((x₀, pk), sk, m)) =
  do{ (cs : vector G n) ← repeat_n ($ᵗ G) n,
      (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
      (h : vector bool n) ← query₂ () (ys, m),
      return (zip_commits_with_hash cs h sk) } := rfl

@[simp]
lemma support_sign (x₀ pk : X) (sk : G) (m : M) :
  ((hhs_signature G X M n).sign ((x₀, pk), sk, m)).support =
    ⋃ (cs : vector G n) (h : vector bool n), { zip_commits_with_hash cs h sk } :=
sorry

end sign

section verify

@[simp]
lemma verify_apply {n : ℕ} (x₀ pk : X) (m : M) (σ : vector (G × bool) n) :
  ((hhs_signature G X M n).verify ((x₀, pk), m, σ)) =
  do{ (h : vector bool n) ← query₂ () (retrieve_commits x₀ pk σ, m),
      return (h = σ.map prod.snd) } := rfl

end verify

section is_valid_signature

/-- Check if a signature is valid, given an explicit internal state of the random oracle.
Note that we return `false` for things not-previously queried,
which differs from e.g. the behaviour of the actual `unforgeable` experiment. -/
def is_valid_signature (x₀ pk : X) (m : M) (σ : vector (G × bool) n)
  (cache : query_log ((vector X n × M) ↦ₒ vector bool n)) : Prop :=
match cache.lookup () (retrieve_commits x₀ pk σ, m) with
| none := true
| (some h) := h = σ.map prod.snd
end

/-- Sign always returns valid signatures, in terms of the final random oracle state. -/
lemma is_valid_signature_of_mem_support_sign (x₀ pk : X) (sk : G) (m : M)
  (σ : vector (G × bool) n) (cache : query_log (hhs_signature G X M n).random_oracle_spec)
  (h : (σ, (), cache) ∈ (default_simulate (idₛ ++ₛ random_oracle _) $
    (hhs_signature G X M n).sign ((x₀, pk), sk, m)).support) :
  is_valid_signature x₀ pk m σ cache :=
begin
  sorry
end

/-- Given a valid signature for some random oracle state, verify returns true
assuming the state is initialized with that cache. -/
lemma support_verify_of_is_valid_signature (x₀ pk : X) (m : M)
  (σ : vector (G × bool) n) (cache : query_log (hhs_signature G X M n).random_oracle_spec)
  (h : is_valid_signature x₀ pk m σ cache) : (simulate (idₛ ++ₛ random_oracle _)
    ((hhs_signature G X M n).verify ((x₀, pk), m, σ)) ((), cache)).support = {(tt, (), cache)} :=
begin
  sorry
end

end is_valid_signature

section complete

theorem hhs_signature_complete [inhabited G] :
  (hhs_signature G X M n).complete :=
begin
  rw signature.complete_iff_signatures_support_subset,
  rintros m ⟨x₀, pk⟩ sk σ hgen hsign,
  sorry
end

end complete

section unforgeable_reductions

variables (x₀ pk : X) (adversary : (hhs_signature G X M n).unforgeable_adversary)

section mock_signing_oracle

/-- Oracle to mock a signing oracle for messages in the vectorization reduction.
Predetermines the random oracle results to fake a valid signature,
keeping the results in a seperate internal mocked cache.
Queries to the random oracle are first filtered through this,
and are passed to the true random oracle only if the query is fresh. -/
def mock_signing_oracle : sim_oracle (hhs_signature G X M n).unforgeable_adversary_oracle_spec
  (hhs_signature G X M n).base_oracle_spec
  (query_log (hhs_signature G X M n).random_oracle_spec) :=
{ default_state := query_log.init _,
  o := λ i, match i with
    -- For uniform selection queries, simply forward them to the lower level.
    | (sum.inl (sum.inl i)) := λ ⟨t, mock_cache⟩,
      do{ u ← query (sum.inl i) t,
          return (u, mock_cache) }
    -- For random oracle queries, check if the query has been mocked.
    -- If so, return the mocked value, otherwise call the regular random oracle
    | (sum.inl (sum.inr i)) := λ ⟨t, mock_cache⟩, mock_cache.lookup_cached_or_run i t
      (@query (hhs_signature G X M n).base_oracle_spec (sum.inr i) t)
    | (sum.inr ()) := λ ⟨m, mock_cache⟩,
      do{ bs ← repeat_n ($ᵗ bool) n, -- pre-select what all the bool results will be.
          cs ← repeat_n ($ᵗ G) n,
          ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
          mock_cache' ← return (mock_cache.log_query () (ys, m) bs),
          return (vector.zip_with prod.mk cs bs, mock_cache') }
  end }

end mock_signing_oracle

section mock_signing_reduction

/-- Fake the signing oracle, and force a query corresponding to adversary's result. -/
def mock_signing_reduction :
  oracle_comp (hhs_signature G X M n).base_oracle_spec (M × vector (G × bool) n) :=
do{ ⟨m, σ⟩ ← default_simulate' (mock_signing_oracle x₀ pk) (adversary.adv (x₀, pk)),
    _ ← query₂ () (retrieve_commits x₀ pk σ, m), -- force a query to the final output
    return (m, σ) }

/-- Further simulate the random oracle after mocking the signing oracle-/
def simulate_mock_signing_reduction : oracle_comp uniform_selecting (M × vector (G × bool) n ×
  query_log (hhs_signature G X M n).random_oracle_spec) :=
do{ ⟨⟨m, σ⟩, (), cache⟩ ← default_simulate (idₛ ++ₛ random_oracle _)
      (mock_signing_reduction x₀ pk adversary),
    return (m, σ, cache) }

theorem prob_event_is_valid_signature_ge_unforgeable_advantage  :
  ⦃λ ⟨m, σ, cache⟩, is_valid_signature x₀ pk m σ cache |
    simulate_mock_signing_reduction x₀ pk adversary⦄
      ≥ adversary.advantage :=
begin
  sorry
end

end mock_signing_reduction

section choose_fork

/- The choose_fork that will be passed to forking lemma. `q` will be the
max queries of the adversary (given by its `query_bound`).
Returns none if it hasn't been queried or if the signature isn't valid.

Note that if the message was queried to signing oracle (causing the experiment to fail
for unforgeability), then the result will only be in the higher level cache,
not the lower level one being used here (since it never leaves the "mock") -/
def choose_fork (m : M) (σ : vector (G × bool) n)
  (cache : query_log (hhs_signature G X M n).random_oracle_spec) (q : ℕ) : option (fin q) :=
match cache.lookup_with_index () (retrieve_commits x₀ pk σ, m) with
| none := none
| (some ⟨h, index⟩) := if hq : index < q ∧ h = σ.map prod.snd then some ⟨index, hq.1⟩ else none
end

end choose_fork

section fork_reduction

/-- Reduce an unforgeability adversery to a forking adversary that can be passed to
`oracle_comp.fork` to get two results, that can be used to construct a adversary for
vectorization in the hard homogenous space.
`q` is the maximum number of queries made by the adversary to consider. -/
def forking_adversary_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  forking_adversary (vector X n × M) (vector bool n) (M × vector (G × bool) n) :=
{ adv := mock_signing_reduction x₀ pk adversary,
  q := adversary.query_bound,
  choose_fork := λ ⟨m, σ⟩ log, choose_fork x₀ pk m σ log (adversary.query_bound),
  cache_nonempty := sorry,
  no_overflow := sorry }

/-- The forked adversary reduction succeeds at least as often as the original -/
theorem forking_adversary_reduction_advantage :
  (forking_adversary_reduction x₀ pk adversary).advantage ≥ adversary.advantage :=
calc (forking_adversary_reduction x₀ pk adversary).advantage
  = ⦃λ ⟨m, σ, cache⟩, is_valid_signature x₀ pk m σ cache |
      simulate_mock_signing_reduction x₀ pk adversary⦄ :
    sorry
  ... ≥ adversary.advantage :
    prob_event_is_valid_signature_ge_unforgeable_advantage x₀ pk adversary

variables (i : option $ fin adversary.query_bound) (m m' : M)
  (cache cache' : query_log (hhs_signature G X M n).random_oracle_spec)
  (σ σ' : vector (G × bool) n)

section lookup

/-- `choose_fork` forces the resulting cache to have a query
matching the resulting `bool`s in the signature -/
theorem lookup_left_eq_signature_bools (hi : i.is_some)
  (h : (i, (m, σ), cache, (m', σ'), cache') ∈
    (fork (forking_adversary_reduction pk x₀ adversary)).support) :
  cache.lookup () (retrieve_commits x₀ pk σ, m) = some (σ.map prod.snd) :=
begin
  sorry
end

/-- `choose_fork` forces the resulting cache to have a query
matching the resulting `bool`s in the signature -/
theorem lookup_right_eq_signature_bools (hi : i.is_some)
  (h : (i, (m, σ), cache, (m', σ'), cache') ∈
    (fork (forking_adversary_reduction pk x₀ adversary)).support) :
  cache'.lookup () (retrieve_commits x₀ pk σ', m') = some (σ'.map prod.snd) :=
begin
  sorry
end

/-- If the fork succeeds at giving different outputs at the forked query,
then that must be true for the signature's commits, by definition of `choose_fork`. -/
theorem lookup_ne_lookup_of_cache_differs (hi : i.is_some)
  (h : (i, (m, σ), cache, (m', σ'), cache') ∈
    (fork (forking_adversary_reduction pk x₀ adversary)).support)
  (h' : forked_cache_differs (i, (m, σ), cache, (m', σ'), cache')) :
  cache'.lookup () (retrieve_commits x₀ pk σ', m') ≠
    cache.lookup () (retrieve_commits x₀ pk σ, m) :=
begin
  sorry
end

end lookup

/-- If fork returns a non-`none` index, then the inputs to the oracle must also match,
in particular the output of `retrieve_commits` must also match,
since `choose_fork` uses this to decide which oracle to fork on. -/
theorem retrieve_commits_eq_retrieve_commits (hi : i.is_some)
  (h : (i, (m, σ), cache, (m', σ'), cache') ∈
    (fork (forking_adversary_reduction pk x₀ adversary)).support) :
  retrieve_commits x₀ pk σ = retrieve_commits x₀ pk σ' :=
begin
  sorry
end

/-- If the forked caches differ, then so must the booleans in the resulting signature,
since they must be exactly the outputs of the oracle for signing to succeed -/
theorem oracle_output_ne_oracle_output (hi : i.is_some)
  (h : (i, (m, σ), cache, (m', σ'), cache') ∈
    (fork (forking_adversary_reduction pk x₀ adversary)).support)
  (h' : forked_cache_differs (i, (m, σ), cache, (m', σ'), cache')) :
  σ.map prod.snd ≠ σ'.map prod.snd :=
begin
  sorry
end

/-- If the fork succeeds, we know that there are two valid signatures
corresponding to a query with the same input and a different output.
This further implies that `retrieve_commits` agrees on both,
but the actual booleans are different, which will let us get a vectorization. -/
theorem vectorizable_of_fork_success
  (h : (i, (m, σ), cache, (m', σ'), cache') ∈
    (fork (forking_adversary_reduction pk x₀ adversary)).support)
  (h' : fork_success (i, (m, σ), cache, (m', σ'), cache')) :
  retrieve_commits x₀ pk σ = retrieve_commits x₀ pk σ'
    ∧ σ.map prod.snd ≠ σ'.map prod.snd :=
let ⟨hi, hcache⟩ := h' in
⟨retrieve_commits_eq_retrieve_commits x₀ pk _ i m m' cache cache' σ σ' hi h,
  oracle_output_ne_oracle_output x₀ pk _ i m m' cache cache' σ σ' hi h hcache⟩

/-- The probability of the fork succeeding is at least the square of
the original adversary's success probability, minus a small chance
of both oracle calls giving the same result. -/
theorem prob_event_fork_success_reduction (x₀ pk : X)
  (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  ⦃fork_success | fork (forking_adversary_reduction pk x₀ adversary)⦄ ≥
    (adversary.advantage ^ 2 / (adversary.query_bound)) - (1 / 2 ^ n) :=
calc ⦃fork_success | fork (forking_adversary_reduction pk x₀ adversary)⦄
  ≥ ((forking_adversary_reduction pk x₀ adversary).advantage ^ 2 / (adversary.query_bound))
      - (1 / (fintype.card $ vector bool n)) :
    prob_event_fork_success (forking_adversary_reduction pk x₀ adversary)
  ... ≥ ((forking_adversary_reduction pk x₀ adversary).advantage ^ 2 /
          (adversary.query_bound)) - (1 / 2 ^ n) :
    begin
      rw [card_vector, fintype.card_bool, nat.cast_pow, nat.cast_two],
      exact le_rfl
    end
  ... ≥ (adversary.advantage ^ 2 / (adversary.query_bound)) - (1 / 2 ^ n) :
    sorry
  
end fork_reduction

section vectorization_reduction

def vectorization_of_signatures (σ σ' : vector (G × bool) n) : G :=
(σ.to_list.zip σ'.to_list).foldr (λ ⟨⟨g₀, b⟩, ⟨g₁, b'⟩⟩ g,
  if b then (if b' then g else g₁ - g₀) else (if b' then g₀ - g₁ else g)) (arbitrary G)

theorem vectorization_of_signatures_eq_of_exists_index (σ σ' : vector (G × bool) n)
  (h : retrieve_commits pk x₀ σ = retrieve_commits pk x₀ σ')
  (h' : σ.map prod.snd ≠ σ'.map prod.snd) :
  vectorization_of_signatures σ σ' = pk -ᵥ x₀ :=
begin
  sorry
end

/-- Reduce an unforgeability adversery to a hhs vectorization adversary,
by forking the adversary and using the two different results -/
def vectorization_adversary_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  vectorization_adversary G X :=
{ adv := λ ⟨pk, x₀⟩,
    do{ ⟨i, ⟨m, σ⟩, cache, ⟨m', σ'⟩, cache'⟩ ← fork (forking_adversary_reduction pk x₀ adversary),
        return (vectorization_of_signatures σ σ') } }

theorem main_result (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  ⦃(=) (pk -ᵥ x₀) | (vectorization_adversary_reduction adversary).adv (pk, x₀)⦄ ≥
    (adversary.advantage ^ 2 / adversary.query_bound) - (1 / 2 ^ n)  :=
calc ⦃(=) (pk -ᵥ x₀) | (vectorization_adversary_reduction adversary).adv (pk, x₀)⦄
  = ⦃λ o, (vectorization_of_signatures o.2.1.2 o.2.2.2.1.2) = pk -ᵥ x₀ |
      fork (forking_adversary_reduction pk x₀ adversary)⦄ :
    sorry
  ... ≥ ⦃fork_success | fork (forking_adversary_reduction pk x₀ adversary)⦄ :
    begin
      refine distribution_semantics.prob_event_le_prob_event_of_subset _ _,
      intros o ho,
      -- have := vectorizable_of_fork_success x₀ pk _ _ _ _ _ _ _ _ _ ho,
      apply vectorization_of_signatures_eq_of_exists_index,
      refine (vectorizable_of_fork_success pk x₀ _ _ o.2.1.1 o.2.2.2.1.1 _ _ _ _ sorry ho.1).1,
      refine (vectorizable_of_fork_success pk x₀ _ _ o.2.1.1 o.2.2.2.1.1 _ _ _ _ sorry ho.1).2
    end
  ... ≥ (adversary.advantage ^ 2 / adversary.query_bound) - (1 / 2 ^ n) :
    prob_event_fork_success_reduction x₀ pk _

lemma vectorization_adversary_reduction_advantage
  (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  (vectorization_adversary_reduction adversary).advantage ≥
    (adversary.advantage ^ 2 / adversary.query_bound) - (1 / 2 ^ n) :=
calc (vectorization_adversary_reduction adversary).advantage
  = (∑' pk x₀, ⦃(=) (pk -ᵥ x₀) |
      (vectorization_adversary_reduction adversary).adv (pk, x₀)⦄) / (fintype.card X) ^ 2 :
    vectorization_adversary.advantage_eq_tsum (vectorization_adversary_reduction adversary)
  ... ≥ (∑' (pk x₀ : X), (adversary.advantage ^ 2 / adversary.query_bound - (1 / 2 ^ n))) /
          (fintype.card X) ^ 2 :
    begin
      exact div_le_div_of_le_of_nonneg (tsum_le_tsum (λ pk, tsum_le_tsum
        (λ x₀, by apply main_result) sorry sorry) sorry sorry) zero_le'
    end
  ... = (adversary.advantage ^ 2 / adversary.query_bound) - (1 / 2 ^ n) :
    begin
      simp_rw [tsum_fintype, finset.sum_const, nsmul_eq_mul],
      rw [← mul_assoc, ← pow_two, div_eq_mul_inv, mul_comm, ← mul_assoc],
      have : (↑(fintype.card X) : nnreal) ^ 2 ≠ 0 := sorry,
      erw [inv_mul_cancel this, one_mul],
    end 

end vectorization_reduction

end unforgeable_reductions

end hhs_signature

/-- Construct a signature scheme by incrementing both the hard homogenous space parameter,
and the number of commits made by the signature.
Both are controlled by the same parameter, but this could eventually be generalized -/
def hhs_signature_scheme (G X : ℕ → Type) (M : Type)
  [∀ n, fintype $ G n] [∀ n, fintype $ X n] [∀ n, inhabited $ G n] [∀ n, inhabited $ X n]
  [∀ n, decidable_eq $ G n] [∀ n, decidable_eq $ X n] [decidable_eq M]
  [∀ n, add_group $ G n] [∀ n, algorithmic_homogenous_space (G n) (X n)]
  [hard_homogenous_space G X] : signature_scheme :=
λ n, hhs_signature (G n) (X n) M n

namespace hhs_signature_scheme

section unforgeable

variables (G X : ℕ → Type) (M : Type)
  [∀ n, fintype $ G n] [∀ n, fintype $ X n] [∀ n, inhabited $ G n] [∀ n, inhabited $ X n]
  [∀ n, decidable_eq $ G n] [∀ n, decidable_eq $ X n] [decidable_eq M]
  [∀ n, add_group $ G n] [∀ n, algorithmic_homogenous_space (G n) (X n)]
  [hard_homogenous_space G X]

theorem hhs_signature_scheme_unforgeable : (hhs_signature_scheme G X M).unforgeable :=
begin
  intros adversary _,
  let reduction : Π (sp : ℕ), vectorization_adversary (G sp) (X sp) :=
    λ n, hhs_signature.vectorization_adversary_reduction (adversary n),
  have := hard_homogenous_space.vectorization_hard reduction,
  sorry,
end

end unforgeable

end hhs_signature_scheme