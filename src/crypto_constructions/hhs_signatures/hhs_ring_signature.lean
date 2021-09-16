import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import crypto_foundations.primitives.ring_signatures.ring_signature
import crypto_foundations.primitives.hash_function.hash_function

import data.vector2

/-!
# Hard Homogenous Space based Ring Signature Scheme

This file constructs a ring signature from a hard homogenous space.
Note that the construction requires a hash function into the group G.
-/

section ring_sig_of_pas

variables {M G X K : Type}
  [fintype G] [fintype X] [inhabited G] [inhabited X] 
  [decidable_eq M] [decidable_eq G] [decidable_eq X] [decidable_eq K]
variables [add_comm_group G] [add_action G X]
variables [function_cost_model ℚ] [comp_cost_model ℚ]

-- TODO: Clean this up
structure sig_type (K G : Type) (n : ℕ) : Type :=
(k : K)
(rs : vector G n)
(cs : vector G n)

@[simps]
def ring_sig_of_pas [principal_action_class G X]
  (x₀ : X) (H : hash_function K (list X × M) G) :
  ring_signature M (sig_type K G) X G :=
{ gen := λ _, (do 
    g ← comp.rnd G, 
    return (g +ᵥ x₀, g)),
  gen_well_formed := by apply_instance,
  sign := λ n inp, (do
    k ← H.keygen (),
    tᵢ ← comp.rnd G,
    rs ← comp.vector_call (comp.rnd G) n,
    cs ← comp.vector_call (comp.rnd G) n,
    Ts ← return (vector.of_fn (λ j, (rs.nth j + cs.nth j) +ᵥ inp.R.mems.nth j)),
    Ts' ← return (Ts.update_nth inp.R.i (tᵢ +ᵥ x₀)),
    h ← return (⟨x₀ :: (inp.R.mems.append Ts').to_list, inp.m⟩ : list X × M),
    c ← return (H.hash (k, h)),
    cᵢ ← return (c + cs.nth inp.R.i - cs.to_list.sum),
    rᵢ ← return (tᵢ - inp.sk - cᵢ),
    return ({ k := k, 
        cs := cs.update_nth inp.R.i cᵢ, 
        rs := rs.update_nth inp.R.i rᵢ }
    )),
  sign_well_formed := by apply_instance,
  verify := λ n inp, 
    let Ts : vector X n := vector.of_fn (λ j, (inp.σ.rs.nth j + inp.σ.cs.nth j) +ᵥ inp.mems.nth j) in 
    let h : list X × M := ⟨x₀ :: (inp.mems.append Ts).to_list, inp.m⟩ in 
    H.hash (inp.σ.k, h) = inp.σ.cs.to_list.sum,
  }

variables [principal_action_class G X]
  (x₀ : X) (H : hash_function K (list X × M) G)

@[simp]
lemma ring_sig_of_pas.mem_support_keygen_iff (k : X × G) :
  k ∈ ((ring_sig_of_pas x₀ H).gen ()).support ↔ 
    k.1 = k.2 +ᵥ x₀ :=
begin
  cases k with x g,
  simp,
end

lemma ring_sig_of_pas.vectorization_of_mem_support_keygen
  (k : X × G) (hk : k ∈ ((ring_sig_of_pas x₀ H).gen ()).support) :
    vectorization G x₀ k.1 = k.2 :=
begin
  cases k,
  simp at hk,
  simp [hk],
end

lemma ring_sig_of_pas.vectorization_of_mem_support_keygen'
  (k : X × G) (hk : k ∈ ((ring_sig_of_pas x₀ H).gen ()).support) :
    vectorization G k.1 x₀ = - k.2:=
by rw [vectorization_swap, ring_sig_of_pas.vectorization_of_mem_support_keygen x₀ H k hk]

@[simp]
lemma ring_sig_of_pas.verify_iff (n : ℕ) (inp : verification_input n X M (sig_type K G)) : 
  ((ring_sig_of_pas x₀ H).verify n inp) =
    let Ts : vector X n := vector.of_fn (λ j, (inp.σ.rs.nth j + inp.σ.cs.nth j) +ᵥ inp.mems.nth j) in
    H.hash (inp.σ.k, ⟨vector.to_list (x₀ ::ᵥ (inp.mems.append Ts)), inp.m⟩) = inp.σ.cs.to_list.sum :=
by simp

theorem ring_sig_of_pas.complete [principal_action_class G X]
  (x₀ : X) (H : hash_function K (list X × M) G) :
  (ring_sig_of_pas x₀ H).complete :=
begin
  intros n i m,
  simp only [comp.Pr_def, and_true, bool.forall_bool, implies_true_iff, eq_self_iff_true, comp.Pr_prop_eq_one_iff],
  intro h,
  rw ring_signature.mem_support_completeness_experiment_iff at h,
  obtain ⟨ks, hks, σ, hσ, h⟩ := h,
  suffices : (ring_sig_of_pas x₀ H).verify n ⟨vector.map prod.fst ks, m, σ⟩ = tt,
  from absurd (h.trans this).symm tt_eq_ff_eq_false,
  simp only [vector.to_list_cons, vector.nth_map, vector.to_list_append, vector.to_list_of_fn, ring_sig_of_pas_verify,
    vector.to_list_map, to_bool_iff],
  simp at hσ,
  obtain ⟨k, hk, tᵢ, rs, cs, hσ⟩ := hσ,
  simp [hσ],
  clear hσ,
  refine congr_arg (H.hash) _,
  simp,
  ext j,
  by_cases hj : j = i,
  {
    simp only [hj, vector.nth_update_nth_same, add_sub_cancel'_right, vector.nth_of_fn],
    rw vadd_eq_vadd_iff_left _ tᵢ _ x₀,
    rw ring_sig_of_pas.vectorization_of_mem_support_keygen' x₀ H (ks.nth i) (hks i),
    abel,
  },
  {
    have : i ≠ j := ne.symm hj,
    simp [vector.nth_update_nth_of_ne this, add_comm (cs.nth j) (rs.nth j)],
  },
end

end ring_sig_of_pas

variables {M : Type} {G X K : ℕ → Type}
variables [∀ n, fintype (G n)] [∀ n, fintype (X n)] 
variables [∀ n, inhabited (G n)] [∀ n, inhabited (X n)]
variables [decidable_eq M] [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)] [∀ n, decidable_eq (K n)]
variables [∀ n, add_comm_group (G n)] [∀ n, add_action (G n) (X n)] [∀ n, principal_action_class (G n) (X n)]
variables [function_cost_model ℚ] [pairing_cost_extension ℚ] [comp_cost_model ℚ]

/-- Construct a ring signature scheme from a hard homogenous space.
`x₀` is an arbitrary generator in `X` used as a base for the public keys.
Given security parameter `sp`, a signature on `n` parties is an element
  of type `K sp × vector (G sp) n × vector (G sp) n`.
The first element is the hash key used to sign this, and the two vectors are the signature
TODO: This should probably maybe a bunch of binds instead of let statemest? -/
def ring_signature_scheme_of_hhs [hard_homogeneous_space G X] 
  (x₀ : Π sp, X sp) (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp)) : 
  ring_signature_scheme M (λ sp, sig_type (K sp) (G sp)) X G :=
{
  rs := λ sp, ring_sig_of_pas (x₀ sp) (H.scheme sp),
  gen_poly_time := begin
    simp [ring_sig_of_pas],
    refine complexity_class.polynomial_complexity_bind_of_subsingleton comp _ _,
    {
      exact algorithmic_homogeneous_space.polynomial_complexity_rnd_G X,
    },
    {
      sorry,
    }
  end,
  sign_poly_time := begin
    sorry,
  end,
  verify_poly_time := sorry,
}

variables [hard_homogeneous_space G X] 

-- Either the adversary is forging a hash, or hacking the `c` values.
def unforgeable_reduction (x₀ : Π sp, X sp)
  (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp))
  (p : polynomial ℕ)
  (adv : ring_signature_scheme.unforgeable_adversary
    (ring_signature_scheme_of_hhs x₀ H) p)
  : vectorization_adversary G X × hash_scheme.collision_finding_adversary H :=
⟨{
  A := λ sp, begin
    rintro ⟨x₁, x₂⟩,
    have := ring_signature_scheme.unforgeable_adversary.A adv,
    specialize this sp,
    sorry,
  end,
  is_well_formed := sorry,
  polynomial_complexity := sorry,
}, sorry⟩

theorem ring_signature_scheme_of_hhs.unforgeable (x₀ : Π sp, X sp) 
  (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp))
  (hH : hash_scheme.collision_resistant H) :
  (ring_signature_scheme_of_hhs x₀ H).unforgeable :=
begin
  sorry
end

theorem ring_signature_scheme_of_hhs.anonomyous (x₀ : Π sp, X sp) 
  (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp))
  (hH : hash_scheme.collision_resistant H) :
  (ring_signature_scheme_of_hhs x₀ H).anonomyous :=
begin
  sorry, 
end