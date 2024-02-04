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
open oracle_comp oracle_spec prod vector

variables {G X M : Type} [add_comm_group G] [algorithmic_homogenous_space G X] {n : ℕ}

section zip_commits

/-- Given a list of commitments `cs` and a hash value `h`, zip them together by adding
the secret key to indices of `cs` corresponding to `0` bits in `h`. -/
def zip_commits (sk : G) (gs : vector G n) (bs : vector bool n) : vector G n :=
zip_with (λ c b, if b = tt then c else c + sk) gs bs

variables (sk : G) (gs : vector G n) (bs : vector bool n)

@[simp] lemma nth_zip_commits (i : fin n) : (zip_commits sk gs bs).nth i =
  if bs.nth i = tt then gs.nth i else gs.nth i + sk :=
by rw [zip_commits, zip_with_nth]

@[simp] lemma zip_commits_nil : zip_commits sk nil nil = nil := rfl

@[simp] lemma zip_commits_cons (g : G) (b : bool) : zip_commits sk (g ::ᵥ gs) (b ::ᵥ bs) =
  (if b = tt then g else g + sk) ::ᵥ zip_commits sk gs bs :=
by cases b; simpa only [zip_commits, zip_with, cons_val, list.zip_with]

@[simp] lemma zip_commits_cons' (gs : list G) (bs : list bool) (g : G) (b : bool)
  (hgs : (g :: gs).length = n + 1) (hbs : (b :: bs).length = n + 1) :
  zip_commits sk ⟨g :: gs, hgs⟩ ⟨b :: bs, hbs⟩ =
    (if b = tt then g else g + sk) ::ᵥ zip_commits sk
      ⟨gs, nat.succ_inj'.1 hgs⟩ ⟨bs, nat.succ_inj'.1 hbs⟩ :=
by cases b; simpa only [zip_commits, zip_with, cons_val, list.zip_with]


end zip_commits

section unzip_commits

/-- Given a pair of points `x₀` and `pk`, and a set of commits `zs` zipped with hash `hash`,
map the zipped commits by adding them to `pk` if they correspond to `1` bits in the hash,
and to `x₀` if they correspond to `1` bits in the hash.
Will result in `(cs.map (+ᵥ pk))` if the original values came from `unzip_commits`. -/
def unzip_commits (x₀ pk : X) (zs : vector G n) (hash : vector bool n) : vector X n :=
zs.zip_with (λ z b, if b = tt then z +ᵥ pk else z +ᵥ x₀) hash

variables (x₀ pk : X)  (zs : vector G n) (hash : vector bool n)

@[simp] lemma nth_unzip_commits (i : fin n) : (unzip_commits x₀ pk zs hash).nth i =
  if hash.nth i = tt then zs.nth i +ᵥ pk else zs.nth i +ᵥ x₀ :=
by rw [unzip_commits, zip_with_nth]

@[simp] lemma unzip_commits_nil : unzip_commits x₀ pk (nil : vector G 0) nil = nil := rfl

@[simp] lemma unzip_commits_cons (z : G) (b : bool) :
  unzip_commits x₀ pk (z ::ᵥ zs) (b ::ᵥ hash) =
    (if b = tt then z +ᵥ pk else z +ᵥ x₀) ::ᵥ unzip_commits x₀ pk zs hash :=
by cases b; simpa only [unzip_commits, zip_with, cons_val, list.zip_with]

@[simp] lemma unzip_commits_cons' (zs : list G) (bs : list bool) (z : G) (b : bool)
  (hzs : (z :: zs).length = n + 1) (hbs : (b :: bs).length = n + 1) :
  unzip_commits x₀ pk ⟨z :: zs, hzs⟩ ⟨b :: bs, hbs⟩ =
    (if b = tt then z +ᵥ pk else z +ᵥ x₀) ::ᵥ unzip_commits x₀ pk
      ⟨zs, nat.succ_inj'.1 hzs⟩ ⟨bs, nat.succ_inj'.1 hbs⟩ :=
by cases b; simpa only [unzip_commits, zip_with, cons_val, list.zip_with]

end unzip_commits

section unzip_commits_zip_commits

variables (cs : vector G n) (x₀ pk : X) (sk : G) (hash : vector bool n)

@[simp] lemma nth_unzip_commits_zip_commits (i : fin n) :
  (unzip_commits x₀ pk (zip_commits sk cs hash) hash).nth i =
    if hash.nth i = tt then cs.nth i +ᵥ pk else (cs.nth i + sk) +ᵥ x₀ :=
by by_cases hb : hash.nth i = tt; simp [hb]

@[simp] lemma unzip_commits_zip_commits : unzip_commits x₀ pk (zip_commits sk cs hash) hash =
  cs.zip_with (λ c b, if b = tt then c +ᵥ pk else (c + sk) +ᵥ x₀) hash :=
vector.ext (λ i, by by_cases hb : hash.nth i = tt; simp [hb])

end unzip_commits_zip_commits

namespace hhs_signature

section vec_of_sigs

/-- Given two signatures get the expected secret key used in generating them.
If both signatures are different but both are valid, this outputs a valid vectorization.
In the cases of mismatched bits, we subtract the two group elements.
Otherwise we recurse on the tails of the vectors -/
def vec_of_sigs : Π {n : ℕ}, vector G n × vector bool n →
    vector G n × vector bool n → G
| 0 ⟨⟨[], _⟩, ⟨[], _⟩⟩ ⟨⟨[], _⟩, ⟨[], _⟩⟩ := 0
| (n + 1) ⟨⟨z :: zs, _⟩, ⟨tt :: bs, _⟩⟩
    ⟨⟨z' :: zs', _⟩, ⟨ff :: bs', _⟩⟩ := z' - z
| (n + 1) ⟨⟨z :: zs, _⟩, ⟨ff :: bs, _⟩⟩
    ⟨⟨z' :: zs', _⟩, ⟨tt :: bs', _⟩⟩ := z - z'
| (n + 1) ⟨⟨_, hzs⟩, ⟨_, hbs⟩⟩ ⟨⟨_, hzs'⟩, ⟨_, hbs'⟩⟩ :=
    vec_of_sigs (tail ⟨_, hzs⟩, tail ⟨_, hbs⟩)
      (tail ⟨_, hzs'⟩, tail ⟨_, hbs'⟩)

@[simp] lemma vector.cons_eq_cons {α : Type} {n : ℕ} (x y : α) (xs ys : vector α n) :
  x ::ᵥ xs = y ::ᵥ ys ↔ x = y ∧ xs = ys :=
by cases xs; cases ys; simp [cons]

/-- If the two hash values differ (and so in particular one of the bits differs),
and both commits are unzipped the same way, then we can get a valid vectorization. -/
lemma vec_of_sigs_eq_vsub (x₀ pk : X) : ∀ (n : ℕ)
  {zs zs' : vector G n} {hash hash' : vector bool n} (h1 : hash ≠ hash')
  (h2 : unzip_commits x₀ pk zs hash = unzip_commits x₀ pk zs' hash'),
  vec_of_sigs (zs, hash) (zs', hash') = pk -ᵥ x₀
| 0 ⟨[], _⟩ ⟨list.nil, _⟩ ⟨list.nil, _⟩ ⟨list.nil, _⟩ h1 h2 :=
    (h1 ((vector.eq_nil _).trans (vector.eq_nil _).symm)).elim
| (n + 1) ⟨z :: zs, hzs⟩ ⟨z' :: zs', hzs'⟩ ⟨b :: bs, hbs⟩ ⟨b' :: bs', hbs'⟩ h1 h2 :=
  begin
    cases b; cases b'; simp only [vec_of_sigs, tail],
    { simp only [unzip_commits_cons', if_false, vector.cons_eq_cons, vadd_right_cancel_iff,
        ne.def, subtype.mk_eq_mk, eq_self_iff_true, true_and] at h1 h2,
      exact vec_of_sigs_eq_vsub n (λ h, h1 (subtype.mk_eq_mk.1 h)) h2.2 },
    { simp_rw [unzip_commits_cons', eq_self_iff_true, if_false, if_true, vector.cons_eq_cons,
        vadd_eq_vadd_iff_sub_eq_vsub, ← neg_sub z, neg_eq_iff_eq_neg, neg_vsub_eq_vsub_rev] at h2,
      exact h2.1 },
    { simp only [vadd_eq_vadd_iff_sub_eq_vsub, unzip_commits_cons', eq_self_iff_true,
        if_true, if_false, vector.cons_eq_cons] at h2,
      exact h2.1 },
    { simp only [unzip_commits_cons', if_false, vector.cons_eq_cons, vadd_right_cancel_iff,
        ne.def, subtype.mk_eq_mk, eq_self_iff_true, true_and] at h1 h2,
      exact vec_of_sigs_eq_vsub n (λ h, h1 (subtype.mk_eq_mk.1 h)) h2.2 }
end

end vec_of_sigs

end hhs_signature