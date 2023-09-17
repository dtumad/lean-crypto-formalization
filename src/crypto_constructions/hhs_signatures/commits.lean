/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.zip
import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.fork.fork

/-!
# Commit Functions for Hard Homogenous Space Signatures

-/

open_locale ennreal big_operators
open oracle_comp oracle_spec prod algorithmic_homogenous_space

section commits

variables {G X M : Type} [add_group G] [algorithmic_homogenous_space G X] {n : ℕ}

/-- Given a list of commitments `cs` and a hash value `h`, zip them together by adding
the security key to indices of `cs` corresponding to `0` bits in `h`. -/
@[reducible, inline] def zip_commits (cs : vector G n)
  (hv : vector bool n) (sk : G) : vector (G × bool) n :=
vector.zip_with (λ c b, (if b = tt then c else c + sk, b)) cs hv

/-- Given a pair of points `x₀` and `pk`, attempt to retreive the commits from a signature `σ`,
by adding the vector to either `pk` or `x₀` depending on if the entry would have had `sk` added.
Will result in `(cs.map (+ᵥ pk))` if the original signature is valid. -/
@[reducible, inline] def retrieve_commits (x₀ pk : X)
  (σ : vector (G × bool) n) : vector X n :=
(σ.map (λ s, if s.2 = tt then s.1 +ᵥ pk else s.1 +ᵥ x₀))

lemma nth_retrieve_commits_zip_commits (x₀ pk : X)
  (cs : vector G n) (hv : vector bool n) (sk : G) (i : fin n) :
  (retrieve_commits x₀ pk (zip_commits cs hv sk)).nth i =
    if hv.nth i = tt then cs.nth i +ᵥ pk else (cs.nth i + sk) +ᵥ x₀:=
by by_cases hv : hv.nth i = tt; simp [hv]

lemma retrieve_commits_zip_commits_vadd (x₀ : X) (sk : G) (cs : vector G n) (hv : vector bool n) :
  retrieve_commits x₀ (sk +ᵥ x₀) (zip_commits cs hv sk) = cs.map (+ᵥ (sk +ᵥ x₀)) :=
vector.ext (λ i, by rw [nth_retrieve_commits_zip_commits, vadd_vadd,
  if_t_t, vector.nth_map, vadd_vadd])

-- lemma retrieve_commits_zip_commits_vadd (x₀ pk : X) (sk : G) (cs : vector G n) (hv : vector bool n) :
--   retrieve_commits x₀ (sk +ᵥ x₀) (zip_commits cs hv sk) = cs.map (+ᵥ (sk +ᵥ x₀)) :=
-- vector.ext (λ i, by rw [nth_retrieve_commits_zip_commits, vadd_vadd,
--   if_t_t, vector.nth_map, vadd_vadd])

/-- `retrieve_commits` will succeed if every hash bit is `0` or if `sk` is a true vectorization. -/
@[simp] lemma retrieve_commits_zip_commits_eq_iff (x₀ pk : X)
  (cs : vector G n) (hv : vector bool n) (sk : G) :
  (retrieve_commits x₀ pk (zip_commits cs hv sk) = (cs.map (+ᵥ pk))) ↔
    hv = vector.replicate n tt ∨ sk +ᵥ x₀ = pk :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    rw [zip_commits, retrieve_commits] at h,
    have : ∃ i, vector.nth hv i = ff := sorry,
    sorry,
    -- rw [imp_iff_not]
  },
  {
    sorry,
  }
end

section vectorization_of_signatures

/-- Given two signatures get the expected secret key used in generating them.
If both signatures are different but both are valid, this outputs a valid vectorization. -/
def vectorization_of_signatures (σ σ' : vector (G × bool) n) : G :=
let zs : option ((G × bool) × (G × bool)) :=
  list.find (λ z, z.1.2 ≠ z.2.2) (list.zip_with prod.mk σ.1 σ'.1) in
match zs with
| none := 0 -- Failure case if no bits differ
| (some ⟨⟨g1, b1⟩, ⟨g2, b2⟩⟩) := if b1 then g1 - g2 else g2 - g1
end

/-- Correctness of `vectorization_of_signatures` in finding a valid `vectorization`,
assuming both signatures differ -/
lemma vectorization_of_signatures_of_ne (x₀ pk : X) (σ σ' : vector (G × bool) n)
  (h1 : σ.map snd ≠ σ'.map snd) (h2 : retrieve_commits x₀ pk σ = retrieve_commits x₀ pk σ') :
  vectorization_of_signatures σ σ' = pk -ᵥ x₀ :=
begin
  sorry
end

end vectorization_of_signatures

end commits