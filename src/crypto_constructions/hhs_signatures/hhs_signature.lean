import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.repeat_n
import data.vector.zip

open oracle_comp oracle_spec

variables {G X M : Type} [fintype G] [fintype X] [inhabited X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [add_action G X] [algorithmic_homogenous_space G X]

/-- Function used in signing to combine the random commitments with the resulting hash,
  using the provided secret key to prove that the secret key corresponds to the public key -/
@[reducible, inline]
def zip_commits_with_hash {n : ℕ} (cs : vector G n) (h : vector bool n) (sk : G) :
  vector (G × bool) n :=
vector.zip_with (λ c (b : bool), (if b then c else c + sk, b)) cs h

lemma zip_commits_with_hash_zero (sk : G) :
  zip_commits_with_hash vector.nil vector.nil sk = vector.nil :=
rfl

@[reducible, inline]
def retrieve_commits (x₀ : X) {n : ℕ} (σ : vector (G × bool) n) (pk : X) :
  vector X n :=
(σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀))

lemma retrieve_commits_zero (x₀ : X) (pk : X) :
  retrieve_commits x₀ (@vector.nil $ G × bool) pk = vector.nil :=
rfl

variables (G X M)

/-- Signature derived from a hard homogenous space, based on the diffie helmann case.
  `n` represents the number of commitments to make, more corresponding to more difficult forgery.
  `x₀` is some arbitrary public base point in `X`, used to compute public keys from secret keys
  TODO: we need some way to declare that the second oracle is a
    "random oracle" for completeness to even hold.
    should include `x₀` in the public key, generated randomly uniformly -/
noncomputable def hhs_signature (n : ℕ) :
  signature M (X × X) G (vector (G × bool) n) :=
{ random_oracles := ((vector X n × M) →ₒ vector bool n),
  random_oracles_finite_range := singleton_spec.finite_range _ _,
  random_oracles_computable := singleton_spec.computable _ _,
  gen := λ _, do {
    x₀ ←$ᵗ X,
    sk ←$ᵗ G,
    return ((x₀, sk +ᵥ x₀), sk)
  },
  sign := λ ⟨⟨x₀, pk⟩, sk, m⟩, do {
    (cs : vector G n) ← repeat_n ($ᵗ G) n,
    (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
    (h : vector bool n) ← query (sum.inr ()) (ys, m),
    return (zip_commits_with_hash cs h sk)
  },
  verify := λ ⟨⟨x₀, pk⟩, m, σ⟩, do {
    (ys : vector X n) ← return (retrieve_commits x₀ σ pk),
    (h : vector bool n) ← query (sum.inr ()) (ys, m),
    return (h = σ.map prod.snd) 
  },
  gen_poly_time := sorry,
  sign_poly_time := sorry,
  verify_poly_time := sorry }

variables {G X M}

namespace signature_of_principal_action_class 
 
variables [algorithmic_homogenous_space G X] (n : ℕ)

/-- We can coerce any uniform selection computation up to one for the oracles of `hhs_signature` -/
noncomputable instance coe_uniform_selecting_oracles (A : Type) :
  has_coe (oracle_comp uniform_selecting A)
    (oracle_comp (hhs_signature G X M n).oracles A) :=
⟨λ oa, @has_coe.coe _ _ (coe_append_right uniform_selecting _ A) oa⟩
 
/-- TODO: must be a better way to make this easy?-/
@[simp]
lemma support_coe_uniform_selecting_oracles {A : Type} (oa : oracle_comp uniform_selecting A) :
  support (oa : oracle_comp (hhs_signature G X M n).oracles A) = oa.support :=
begin
  sorry
end

@[simp]
lemma gen_apply (u : unit) :
  ((hhs_signature G X M n).gen u) = do { x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk) } :=
rfl

lemma support_gen :
  ((hhs_signature G X M n).gen ()).support =
    ⋃ (x₀ : X) (sk : G), { ((x₀, sk +ᵥ x₀), sk) } :=
by simp only [gen_apply, support_bind_bind, support_coe_uniform_selecting_oracles,
  support_uniform_select_fintype, support_pure, set.Union_true]

@[simp]
lemma sign_apply (x₀ : X) (pk : X) (sk : G) (m : M) :
  ((hhs_signature G X M n).sign ((x₀, pk), sk, m)) = do {
    (cs : vector G n) ← repeat_n ($ᵗ G) n,
    (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
    (h : vector bool n) ← query (sum.inr ()) (ys, m),
    return (zip_commits_with_hash cs h sk)
  } :=
rfl

@[simp]
lemma support_sign (x₀ : X) (pk : X) (sk : G) (m : M) :
  ((hhs_signature G X M n).sign ((x₀, pk), sk, m)).support =
    ⋃ (cs : vector G n) (h : vector bool n), { zip_commits_with_hash cs h sk } :=
sorry

@[simp]
lemma verify_apply {n : ℕ} (x₀ : X) (pk : X) (m : M) (σ : vector (G × bool) n) :
  ((hhs_signature G X M n).verify ((x₀, pk), m, σ)) = do {
    (ys : vector X n) ← return (retrieve_commits x₀ σ pk),
    (h : vector bool n) ← query (sum.inr ()) (ys, m),
    return (h = σ.map prod.snd) 
  } :=
rfl

theorem signature_of_principal_action_class_complete :
  (hhs_signature G X M n).complete :=
begin
  rw signature.complete_iff_signatures_support_subset,
  rintros m ⟨x₀, pk⟩ sk σ hgen hsign,
  sorry
end

-- The choose_fork that will be passed to forking lemma
-- `q` will be the max queries of the adversary
def choose_fork {q : ℕ} (x₀ : X) (n : ℕ) (pk : X) (m : M) 
  (σ : vector (G × bool) n) (log : query_log $ ((vector X n × M) →ₒ vector bool n)) : 
  option (fin q) :=
let index' : option ℕ := log.index_of_input ()
  (σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀), m) in
match index' with
| none := none
| (some index) := if h : index < q then some ⟨index, h⟩ else none
end

def hard_homogenous_space_reduction
  (adversary : signature.unforgeable_adversary $ hhs_signature G X M n) :
  vectorization_adversary G X :=
{
  -- We want to set `pk := x` and `x₀ := x'` (TODO: what we really want is `x₀` in `pk` instead of general parameter).
  -- Then forking the adversary get `c` and `c'` with `c +ᵥ x = c' +ᵥ x'`.
  -- We can then take `c - c'` ad the vectorization
  adv := λ ⟨x, x'⟩, begin
    sorry
  end,
  adv_poly_time := sorry
}


end signature_of_principal_action_class