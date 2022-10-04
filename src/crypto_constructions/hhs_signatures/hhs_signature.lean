import data.vector.zip

import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.repeat_n

open oracle_comp oracle_spec

section commits

variables {G X M : Type} [fintype G] [fintype X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X]

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

end commits

-- variables (G X M)

/-- Signature derived from a hard homogenous space, based on the diffie helmann case.
  `n` represents the number of commitments to make, more corresponding to more difficult forgery.
  `x₀` is some arbitrary public base point in `X`, used to compute public keys from secret keys -/
noncomputable def hhs_signature (G X M : Type) [fintype G] [fintype X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M] [add_group G]
  [algorithmic_homogenous_space G X] : signature_scheme :=
λ n, { M := M, PK := X × X, SK := G, S := vector (G × bool) n,
  decidable_eq_M := by apply_instance,
  decidable_eq_S := by apply_instance,
  inhabited_S := by apply_instance,
  random_oracle_spec := ((vector X n × M) ↦ₒ vector bool n),
  random_oracle_spec_finite_range := singleton_spec.finite_range _ _,
  random_oracle_spec_computable := singleton_spec.computable _ _,
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
}

namespace hhs_signature 

variables {G X M : Type} [fintype G] [fintype X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [algorithmic_homogenous_space G X] (n : ℕ)
 
/-- TODO: must be a better way to make this easy?-/
@[simp]
lemma support_coe_uniform_selecting_oracles [inhabited G] {α : Type}
  (oa : oracle_comp uniform_selecting α) :
  support (↑oa : oracle_comp (hhs_signature G X M n).base_oracle_spec α) = oa.support :=
begin
  sorry
end

@[simp]
lemma gen_apply (u : unit) :
  ((hhs_signature G X M n).gen u) = do { x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk) } :=
rfl

lemma support_gen : ((hhs_signature G X M n).gen ()).support =
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

theorem hhs_signature_complete [inhabited G] :
  (hhs_signature G X M n).complete :=
begin
  rw signature.complete_iff_signatures_support_subset,
  rintros m ⟨x₀, pk⟩ sk σ hgen hsign,
  sorry
end

-- The choose_fork that will be passed to forking lemma
-- `q` will be the max queries of the adversary
def choose_fork {q : ℕ} (x₀ : X) (n : ℕ) (pk : X) (m : M) 
  (σ : vector (G × bool) n) (log : query_log $ ((vector X n × M) ↦ₒ vector bool n)) : 
  option (fin q) :=
let index' : option ℕ := log.get_index_of_input ()
  (σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀), m) in
match index' with
| none := none
| (some index) := if h : index < q then some ⟨index, h⟩ else none
end

-- TODO: this should "look like" a regular signature, since the `b` values are still uniform random coins
noncomputable def adversary_sim_oracle [inhabited G] (pk x₀ : X) :
  sim_oracle ((hhs_signature G X M n).unforgeable_adversary_oracle_spec)
    uniform_selecting (query_log (hhs_signature G X M n).random_oracle_spec) :=
{ default_state := query_log.init (hhs_signature G X M n).random_oracle_spec,
  o := λ i, match i with
  | (sum.inr ()) := λ ⟨m, log⟩, do {
    bs ← repeat_n ($ᵗ bool) n, -- pre-select what all the bool results will be
    cs ← repeat_n ($ᵗ G) n,
    ys ← return (vector.zip_with (λ (b : bool) c, if b then c +ᵥ pk else c +ᵥ x₀) bs cs),
    log' ← return (log.log_query () (ys, m) bs),
    return (vector.zip_with prod.mk cs bs, log')
  }
  | (sum.inl i') := λ ⟨t, log⟩, sorry -- TODO: this should run random oracle as usual
  end
}

noncomputable def hhs_signature_vectorization_reduction [inhabited G]
  (adversary : signature.unforgeable_adversary $ hhs_signature G X M n) :
  vectorization.adversary G X :=
{
  -- We want to set `pk := x` and `x₀ := x'` (TODO: what we really want is `x₀` in `pk` instead of general parameter).
  -- Then forking the adversary get `c` and `c'` with `c +ᵥ x = c' +ᵥ x'`.
  -- We can then take `c - c'` ad the vectorization
  adv := λ ⟨x, x'⟩, begin
    refine do {
      σ ← simulate (adversary_sim_oracle n x x') (adversary.adv (x, x')) _,
      sorry
    },
    refine sorry
  end,
  -- adv_poly_time := 
}

end hhs_signature