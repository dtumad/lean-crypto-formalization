/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_constructions.hhs_signatures.hhs_signature

/-!
# Unforgeability of HHS Signature

This file gives an unforgeability proof for `hhs_signature`

-/

namespace hhs_signature

open_locale ennreal big_operators
open oracle_comp oracle_spec algorithmic_homogenous_space hard_homogenous_space

variables {G X M : Type} [fintype G] [fintype X] [inhabited G] [inhabited X]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}


section unforgeable

section mock_signing

/-- Oracle to mock a signing oracle for messages in the vectorization reduction,
mirroring how `signingₛₒ` would respond usually.
Predetermines the random oracle results to fake a valid signature,
keeping the results in a seperate internal mocked cache.
This also includes all caching for the simulation of the random oracles. -/
noncomputable def mock_signingₛₒ (x₀ pk : X) : sim_oracle
  ((hhs_signature G X M n).random_spec ++ (hhs_signature G X M n).signing_spec)
  (uniform_selecting ++ (hhs_signature G X M n).random_spec)
  (query_cache ((vector X n × M) ↦ₒ vector bool n)) :=
{ default_state := ∅,
  o := λ i, match i with
    -- For random oracle queries, check if the query has been mocked.
    -- If so, return the mocked value, otherwise call the regular oracle (caching the result).
    | (sum.inl i) := λ ⟨t, mock_cache⟩, mock_cache.get_or_else i t
        (@query (hhs_signature G X M n).base_spec (sum.inr i) t)
    | (sum.inr ()) := λ ⟨m, mock_cache⟩,
        do {bs ← repeat ($ᵗ bool) n, cs ← repeat ($ᵗ G) n,
          ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
          mock_cache' ← return (mock_cache.cache_query () (ys, m) bs),
          return (vector.zip_with prod.mk cs bs, mock_cache')}
  end }

noncomputable def mock_simulate_signing_oracle (adversary : (hhs_signature G X M n).unforgeable_adversary)
  (x₀ pk : X) : oracle_comp (uniform_selecting ++ (hhs_signature G X M n).random_spec)
    ((M × vector (G × bool) n) × (query_cache ((vector X n × M) ↦ₒ vector bool n))) :=
do {((m, σ), _, mocked_sigs) ← (default_simulate (idₛₒ ++ₛ mock_signingₛₒ x₀ pk) (adversary.run (x₀, pk))),
  return ((m, σ), mocked_sigs)}

def mock_signing_fork_adversary (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  fork_adversary (hhs_signature G X M n).base_spec (X × X)
    ((M × vector (G × bool) n) × (query_cache ((vector X n × M) ↦ₒ vector bool n)))
    (sum.inr ()) (adversary.qb.get_count (sum.inr (sum.inr ()))) :=
sorry
-- fork_adversary.of_choose_input _ _ _

-- { run := λ ⟨x₀, pk⟩, mock_simulate_signing_oracle adversary x₀ pk,
--   choose_fork := begin
--     rintro ⟨x₀, pk⟩ ⟨⟨m, σ⟩, cache⟩,
--   end,
--   qb := sorry,
--   qb_is_bound := sorry,
--   q_eq_bound := sorry }

-- /-- Fake the signing oracle, and force a query corresponding to adversary's result. -/
-- def mock_signing_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary)
--   (x₀ pk : X) : oracle_comp (hhs_signature G X M n).base_oracle_spec
--     (M × vector (G × bool) n) :=
-- do{ ⟨m, σ⟩ ← default_simulate' (idₛₒ ++ₛ mock_signing_sim_oracle x₀ pk) (adversary.run (x₀, pk)),
--     query₂ () (retrieve_commits x₀ pk σ, m), -- force a query to the commit for the final output
--     return (m, σ) }

end mock_signing

variable (adversary : (hhs_signature G X M n).unforgeable_adversary)

/-- Reduce an unforgeability adversery to a forking adversary that can be passed to
`oracle_comp.fork` to get two results, that can be used to construct a adversary for
vectorization in the hard homogenous space.
`q` is the maximum number of queries made by the adversary to consider. -/
def fork_reduction (adversary : (hhs_signature G X M n).unforgeable_adversary) :
  fork_adversary (hhs_signature G X M n).base_spec (X × X)
    ((M × vector (G × bool) n) × (query_cache ((vector X n × M) ↦ₒ vector bool n)))
    sorry sorry :=
sorry
-- fork_adversary.of_choose_input (λ _ _, sorry) (sum.inr ())
--   (λ ⟨x₀, pk⟩ ⟨m, σ⟩, ((retrieve_commits x₀ pk σ, m), σ.map prod.snd))

-- lemma advantage_le_forking_reduction_advantage
--   (adversary : (hhs_signature G X M n).unforgeable_adversary) (x₀ pk : X) :
--     adversary.advantage ≤ (fork_reduction adversary).advantage (x₀, pk) :=
-- begin
--   sorry
-- end

/-- If the fork succeeds, we know that there are two valid signatures
corresponding to a query with the same input and a different output.
This further implies that `retrieve_commits` agrees on both,
but the actual booleans are different, which will let us get a vectorization. -/
theorem vectorizable_of_fork_success'' (x₀ pk : X)
  (fr : fork_result (fork_reduction adversary)) (hfr : fork_success fr)
  (h : fr ∈ (fork (fork_reduction adversary) (x₀, pk)).support) :
  retrieve_commits x₀ pk fr.side_output₁.1.2 = retrieve_commits x₀ pk fr.side_output₂.1.2
    ∧ fr.side_output₁.1.2.map prod.snd ≠ fr.side_output₂.1.2.map prod.snd :=
begin
  sorry
end

/-- The probability of the fork succeeding is at least the square of
the original adversary's success probability, minus a small chance
of both oracle calls giving the same result. -/
theorem le_prob_event_fork_success (x₀ pk : X) :
  (adversary.advantage ^ 2 / (adversary.qb.get_count (sum.inr (sum.inr ())))) - (1 / 2 ^ n) ≤
    ⁅fork_success | fork (fork_reduction adversary) (x₀, pk)⁆ :=
begin
  sorry
end

-- def vectorization_of_commits ()


-- /-- If the fork succeeds, we know that there are two valid signatures
-- corresponding to a query with the same input and a different output.
-- This further implies that `retrieve_commits` agrees on both,
-- but the actual booleans are different, which will let us get a vectorization. -/
-- theorem vectorizable_of_fork_success (x₀ pk : X)
--   (fr : fork_result (fork_reduction adversary)) (hfr : fork_success fr)
--   (h : fr ∈ (fork (fork_reduction adversary) (x₀, pk)).support) :
--   vectorization_of_fork_result _ x₀ pk fr = pk -ᵥ x₀ :=
-- begin
--   sorry
-- end

section vectorization_reduction

noncomputable def vectorization_of_fork_result (adv : (hhs_signature G X M n).unforgeable_adversary)
  (x₀ pk : X) (fr : fork_result (fork_reduction adv)) : G :=
begin
  let σ₁ := fr.side_output₁.1.2,
  let σ₂ := fr.side_output₂.1.2,
  let ys₁ := retrieve_commits x₀ pk fr.side_output₁.1.2,
  let ys₂ := retrieve_commits x₀ pk fr.side_output₂.1.2,
  let h₁ := fr.side_output₁.1.2.map prod.snd,
  let h₂ := fr.side_output₂.1.2.map prod.snd,
  let m : fin n := sorry,
  exact (σ₁.nth m).1 - (σ₂.nth m).1
end

variables {spec : oracle_spec} {α β γ : Type }

example (f : α → β) (oa : oracle_comp spec α) : f <$> oa = do {x ← oa, return (f x)} := rfl
example (og : oracle_comp spec (α → β)) (oa : oracle_comp spec α) :
  og <*> oa = do {g ← og, x ← oa, return (g x)} := rfl

noncomputable def vectorization_reduction (adv : (hhs_signature G X M n).unforgeable_adversary) :
  vectorization_adversary G X :=
{ run :=
  begin
    rintro ⟨x₀, pk⟩,
    have := default_simulate' uniformₛₒ (fork (fork_reduction adv) (x₀, pk)),
    refine vectorization_of_fork_result _ x₀ pk <$> this,
  end
  ,
  qb := sorry,
  qb_is_bound := sorry,
}

/-- The probability of the fork succeeding is at least the square of
the original adversary's success probability, minus a small chance
of both oracle calls giving the same result. -/
theorem le_vectorization_advantage (x₀ pk : X) :
  (adversary.advantage ^ 2 / (adversary.qb.get_count (sum.inr (sum.inr ())))) - (1 / 2 ^ n) ≤
    (vectorization_reduction adversary).advantage :=
begin
  sorry
end

end vectorization_reduction

end unforgeable


end hhs_signature