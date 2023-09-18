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

variables {G X M : Type} [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}

section zip_commits

/-- Given a list of commitments `cs` and a hash value `h`, zip them together by adding
the secret key to indices of `cs` corresponding to `0` bits in `h`. -/
def zip_commits (sk : G) (cs : vector G n) (hash : vector bool n) : vector G n :=
cs.zip_with (λ c b, if b = tt then c else c + sk) hash

variables (cs : vector G n) (sk : G) (hash : vector bool n)

@[simp] lemma nth_zip_commits (i : fin n) : (zip_commits sk cs hash).nth i =
  if hash.nth i = tt then cs.nth i else cs.nth i + sk :=
by rw [zip_commits, vector.zip_with_nth]

end zip_commits

section retrieve_commits

/-- Given a pair of points `x₀` and `pk`, and a set of commits `zs` zipped with hash `hash`,
map the zipped commits by adding them to `pk` if they correspond to `1` bits in the hash,
and to `x₀` if they correspond to `1` bits in the hash.
Will result in `(cs.map (+ᵥ pk))` if the original values came from `retrieve_commits`. -/
def retrieve_commits (x₀ pk : X) (zs : vector G n) (hash : vector bool n) : vector X n :=
zs.zip_with (λ z b, if b = tt then z +ᵥ pk else z +ᵥ x₀) hash

variables (zs : vector G n) (x₀ pk : X) (hash : vector bool n)

@[simp] lemma nth_retrieve_commits (i : fin n) : (retrieve_commits x₀ pk zs hash).nth i =
  if hash.nth i = tt then zs.nth i +ᵥ pk else zs.nth i +ᵥ x₀ :=
by rw [retrieve_commits, vector.zip_with_nth]

lemma retrieve_commits_cons (z : G) (b : bool) :
  retrieve_commits x₀ pk (z ::ᵥ zs) (b ::ᵥ hash) =
    (if b = tt then z +ᵥ pk else z +ᵥ x₀) ::ᵥ retrieve_commits x₀ pk zs hash :=
by cases b; simpa [vector.zip_with, retrieve_commits]

end retrieve_commits

section retrieve_commits_zip_commits

variables (cs : vector G n) (x₀ pk : X) (sk : G) (hash : vector bool n)

lemma nth_retrieve_commits_zip_commits (i : fin n) :
  (retrieve_commits x₀ pk (zip_commits sk cs hash) hash).nth i =
    if hash.nth i = tt then cs.nth i +ᵥ pk else (cs.nth i + sk) +ᵥ x₀ :=
by by_cases hb : hash.nth i = tt; simp [hb]

lemma retrieve_commits_zip_commits : retrieve_commits x₀ pk (zip_commits sk cs hash) hash =
  cs.zip_with (λ c b, if b = tt then c +ᵥ pk else (c + sk) +ᵥ x₀) hash :=
vector.ext (λ i, by by_cases hb : hash.nth i = tt; simp [hb])

end retrieve_commits_zip_commits

section vectorization_of_signatures

open vector

/-- Given two signatures get the expected secret key used in generating them.
If both signatures are different but both are valid, this outputs a valid vectorization. -/
def vectorization_of_zipped_commits :
  Π {n : ℕ}, vector G n → vector G n → vector bool n → vector bool n → G
| 0 ⟨list.nil, _⟩ ⟨list.nil, _⟩ ⟨list.nil, _⟩ ⟨list.nil, _⟩ := 0
| (n + 1) ⟨z :: zs, hzs⟩ ⟨z' :: zs', hzs'⟩ ⟨b :: bs, hbs⟩ ⟨b' :: bs', hbs'⟩ :=
    if b = tt ∧ b' = ff then z' - z
    else if b = ff ∧ b' = tt then z - z'
      else vectorization_of_zipped_commits (vector.tail ⟨_, hzs⟩) (vector.tail ⟨_, hzs'⟩)
        (vector.tail ⟨_, hbs⟩)(vector.tail ⟨_, hbs'⟩)

/-- If the two hash values differ (and so in particular one of the bits differs),
and both commits are unzipped the same way, then we can get a valid vectorization. -/
lemma vectorization_of_zipped_commits_eq_vsub (x₀ pk : X) :
  Π (n : ℕ) (zs zs' : vector G n) (hash hash' : vector bool n)  (h1 : hash ≠ hash')
  (h2 : retrieve_commits x₀ pk zs hash = retrieve_commits x₀ pk zs' hash'),
  vectorization_of_zipped_commits zs zs' hash hash' = pk -ᵥ x₀
| 0 ⟨list.nil, _⟩ ⟨list.nil, _⟩ ⟨list.nil, _⟩ ⟨list.nil, _⟩ h1 h2 :=
    (h1 ((vector.eq_nil _).trans (vector.eq_nil _).symm)).elim
| (n + 1) ⟨z :: zs, hzs⟩ ⟨z' :: zs', hzs'⟩ ⟨b :: bs, hbs⟩ ⟨b' :: bs', hbs'⟩ h1 h2 := begin
  by_cases hb1 : b = tt ∧ b' = ff,
  {
    have := congr_arg (λ v, vector.nth v 0) h2,
    simp [vector.head, hb1.1, hb1.2] at this,
    simp [vectorization_of_zipped_commits, hb1],
    rw [vadd_eq_vadd_iff_sub_eq_vsub] at this,
    exact this,
  },
  by_cases hb2 : b = ff ∧ b' = tt,
  {
    have := congr_arg (λ v, vector.nth v 0) h2,
    simp [vector.head, hb2.1, hb2.2] at this,
    simp [vectorization_of_zipped_commits, hb2],
    rw [← neg_inj, neg_sub, neg_vsub_eq_vsub_rev],
    rw [vadd_eq_vadd_iff_sub_eq_vsub] at this,
    exact this,
  },
  {
    simp [vectorization_of_zipped_commits, hb1, hb2, vector.tail],
    simp at hb1 hb2,
    refine vectorization_of_zipped_commits_eq_vsub n _ _ _ _ _ _,
    {
      simp only [ne.def, subtype.mk_eq_mk, not_and] at h1 ⊢,
      refine h1 _,
      cases b,
      refine symm (hb2 rfl),
      refine symm (hb1 rfl),
    },
    {
      simp [retrieve_commits, vector.zip_with] at h2,
      simp only [retrieve_commits, vector.zip_with, subtype.mk_eq_mk],
      exact h2.2,
    }
  }
end

end vectorization_of_signatures

end commits