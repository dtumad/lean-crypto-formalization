/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_constructions.hhs_signatures.hhs_signature
import computational_monads.query_tracking.query_count.is_query_bound
import computational_monads.simulation_semantics.oracle_append

/-!
# Mocking Signing Oracles for HHS Signatures

This file gives a way to mock the signing oracle for an adversary without an actual secret key.
-/

namespace hhs_signature

open oracle_comp oracle_spec
open sum (inl) (inr)

noncomputable def mock_signing_sim_oracle (G X M : Type) [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] (n : ℕ)
  (x₀ pk : X) : sim_oracle (hhs_signature G X M n).unforgeable_adv_spec
    (unif_spec ++ (unit ↦ₒ vector bool n))
    (bool × query_log ((vector X n × M) ↦ₒ vector bool n)) :=
λ i, match i with
/- For queries to the uniform selection oracle, just forward the queries. -/
| (inl (inl i)) := λ ⟨t, ⟨corrupt, cache⟩⟩, do
  { u ← query (inl i) t,
    return (u, (corrupt, cache)) }
/- For queries to the random oracle, look at the mocked cache. -/
| (sum.inl (inr ())) := λ ⟨⟨xs, m⟩, ⟨corrupt, cache⟩⟩,
  match cache.lookup () (xs, m) with
  | (some bs) := return (bs, (corrupt, cache))
  | none := do { bs ← query (inr ()) (),
      cache' ← return (cache.log_query () (xs, m) bs),
      return (bs, (corrupt, cache')) }
  end
/- For queries to the signing oracle, pre-choose the query result,
  and insert into the cache. "Fails" if `xs` isn't fresh. -/
| (sum.inr ()) := λ ⟨m, ⟨corrupt, cache⟩⟩, do
    { zs ←$ᵗ (vector G n),
      bs ← query (inr ()) (),
      xs ← return (unzip_commits x₀ pk zs bs),
      bad ← return (cache.lookup () (xs, m)).is_some,
      cache' ← return (cache.log_query () (xs, m) bs),
      return ((zs, bs), (corrupt || bad, cache')) }
end

notation `mock_signingₛₒ` := mock_signing_sim_oracle _ _ _ _

variables {α G X M : Type} [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}


end hhs_signature