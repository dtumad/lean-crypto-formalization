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
  [fintype G] [fintype X] 
  [inhabited G] [inhabited X] 
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
  ring_sig M (sig_type K G) X G :=
{ gen := λ _, (do 
    g ← comp.rnd G, 
    return (g +ᵥ x₀, g)),
  gen_well_formed := by apply_instance,
  sign := λ n i sk R m, (do
    k ← H.keygen (),
    tᵢ ← comp.rnd G,
    rs ← comp.vector_call (comp.rnd G) n,
    cs ← comp.vector_call (comp.rnd G) n,
    return (
      let Ts : vector X n := vector.of_fn (λ j, (rs.nth j + cs.nth j) +ᵥ R.nth j) in
      let Ts' : vector X n := Ts.update_nth i (tᵢ +ᵥ x₀) in
      let h : list X × M := ⟨x₀ :: (R.append Ts').to_list, m⟩ in
      let c : G := H.hash (k, h) in
      let cᵢ : G := c + cs.nth i - cs.to_list.sum in
      let rᵢ : G := tᵢ - sk - cᵢ in
      { k := k, 
        cs := cs.update_nth i cᵢ, 
        rs := rs.update_nth i rᵢ }
    )),
  sign_well_formed := by apply_instance,
  verify := λ n R m σ, 
    let Ts : vector X n := vector.of_fn (λ j, (σ.rs.nth j + σ.cs.nth j) +ᵥ R.nth j) in 
    let h : list (X) × M := ⟨x₀ :: (R.append Ts).to_list, m⟩ in 
    H.hash (σ.k, h) = σ.cs.to_list.sum,
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
lemma ring_sig_of_pas.verify_iff (n : ℕ) (R : vector X n) (m : M) 
  (σ : sig_type K G n) :
    ((ring_sig_of_pas x₀ H).verify n R m σ) =
      let Ts : vector X n := vector.of_fn (λ j, (σ.rs.nth j + σ.cs.nth j) +ᵥ R.nth j) in
      H.hash (σ.1, ⟨vector.to_list (x₀ ::ᵥ (R.append Ts)), m⟩) = σ.cs.to_list.sum :=
by simp

theorem ring_sig_of_pas.complete [principal_action_class G X]
  (x₀ : X) (H : hash_function K (list X × M) G) :
  (ring_sig_of_pas x₀ H).complete :=
begin
  intros n i m,
  simp only [comp.Pr_def, and_true, bool.forall_bool, implies_true_iff, eq_self_iff_true, comp.Pr_prop_eq_one_iff],
  intro h,
  rw ring_sig.mem_support_completeness_experiment_iff at h,
  obtain ⟨ks, hks, σ, hσ, h⟩ := h,
  suffices : (ring_sig_of_pas x₀ H).verify n (vector.map prod.fst ks) m σ = tt,
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
    rw principal_action_class.vadd_eq_iff_left _ tᵢ _ x₀,
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
variables [function_cost_model ℚ] [comp_cost_model ℚ]

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
    sorry,
  end,
  sign_poly_time := sorry,
  verify_poly_time := sorry,
}

variables [hard_homogeneous_space G X] 

theorem ring_signature_scheme_of_hhs.anonomyous (x₀ : Π sp, X sp) 
  (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp))
  (hH : hash_scheme.collision_resistant H) :
  (ring_signature_scheme_of_hhs x₀ H).anonomyous :=
begin
  sorry,
end

theorem ring_signature_scheme_of_hhs.unforgeable (x₀ : Π sp, X sp) 
  (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp))
  (hH : hash_scheme.collision_resistant H) :
  (ring_signature_scheme_of_hhs x₀ H).unforgeable :=
begin
  sorry,
end
