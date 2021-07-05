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
  [decidable_eq M] [decidable_eq X] [decidable_eq G] [decidable_eq K]
variables [comm_group G] [mul_action G X]

@[simps]
-- TODO: lemmas about the support of sign
def ring_sig_of_pas [principal_action_class G X]
  (x₀ : X) (H : hash_function K (list X × M) G) :
  ring_sig M (λ n, K × vector G n × vector G n) X G :=
{ gen := (do g ← comp.rnd (G), return (g • x₀, g)),
  gen_well_formed := by apply_instance,
  sign := begin
    refine λ n i sk R m, _,
    refine (comp.rnd G).bind (λ tᵢ, _),
    refine (comp.vector_call (comp.rnd G) n).bind (λ rs, _),
    refine (comp.vector_call (comp.rnd G) n).bind (λ cs, _),
    refine (H.keygen).bind (λ k, _),
    let Ts : vector X n := vector.of_fn (λ j, (rs.nth j * cs.nth j) • R.nth j),
    let Tᵢ : X := tᵢ • x₀,
    let Ts' : vector X n := Ts.update_nth i Tᵢ,
    
    let h : list X × M := ⟨vector.to_list (x₀ ::ᵥ (R.append Ts')), m⟩,
    let c : G := H.hash k h,
    let cᵢ : G := c * (cs.nth i) * ((cs.map (λ g, g⁻¹)).to_list.prod),
    let rᵢ : G := tᵢ * sk * cᵢ⁻¹,
    let cs' : vector G n := cs.update_nth i cᵢ,
    let rs' : vector G n := rs.update_nth i rᵢ,
    exact comp.ret (k, cs', rs'),
  end,
  sign_well_formed := by apply_instance,
  verify := begin
    intros n R m σ,
    let k : K := σ.1,
    let cs : vector G n := σ.2.1,
    let rs : vector G n := σ.2.2,
    let Ts : vector X n := vector.of_fn (λ j, (rs.nth j * cs.nth j) • R.nth j),
    let h : list (X) × M := ⟨vector.to_list (x₀ ::ᵥ (R.append Ts)), m⟩,
    exact H.hash k h = cs.to_list.prod,
  end }

variables [principal_action_class G X]
  (x₀ : X) (H : hash_function K (list X × M) G)

@[simp]
lemma ring_sig_of_pas.mem_support_keygen_iff (k : X × G) :
  k ∈ (ring_sig_of_pas x₀ H).gen.support ↔ 
    k.1 = k.2 • x₀ :=
begin
  cases k with x g,
  simp,
end

lemma ring_sig_of_pas.vectorization_of_mem_support_keygen
  (x : X) (g : G) (hk : (x, g) ∈ (ring_sig_of_pas x₀ H).gen.support) :
    vectorization x x₀ = g :=
begin
  simp at hk,
  simp [hk],
end

lemma ring_sig_of_pas.vectorization_of_mem_support_keygen'
  (k : X × G) (hk : k ∈ (ring_sig_of_pas x₀ H).gen.support) :
    vectorization k.1 x₀ = k.2 :=
begin
  cases k,
  exact ring_sig_of_pas.vectorization_of_mem_support_keygen x₀ H _ _ hk,
end

@[simp]
lemma ring_sig_of_pas.verify_iff (n : ℕ) (R : vector X n) (m : M) 
  (σ : K × vector G n × vector G n) :
    ((ring_sig_of_pas x₀ H).verify n R m σ) =
      let Ts : vector X n := vector.of_fn (λ j, (σ.2.2.nth j * σ.2.1.nth j) • R.nth j) in
      H.hash σ.1 ⟨vector.to_list (x₀ ::ᵥ (R.append Ts)), m⟩ = σ.2.1.to_list.prod :=
by simp

@[simp]
lemma vector.prod_update_nth {G : Type} [group G] {n : ℕ}
  (v : vector G n) (i : fin n) (g : G) :
  (v.update_nth i g).to_list.prod = 
    v.to_list.prod * (v.nth i)⁻¹ * g :=
begin
  sorry,
end

@[simp]
lemma list.prod_map_inv {G : Type} [comm_group G] (gs : list G): 
  (gs.map (λ g, g⁻¹)).prod = gs.prod⁻¹ :=
begin
  sorry,
end

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
  obtain ⟨tᵢ, rs, cs, k, hk, hσ⟩ := hσ,
  simp [hσ],
  clear hσ,
  sorry,
  -- abel,
  -- rw group_prod_thing _ i cs,
  -- congr,
  -- ext j,
  -- have hkj : ks.nth j ∈ (ring_sig_of_pas x₀ H).gen.support,
  -- from hks _ (vector.nth_mem _ _),
  -- split_ifs,
  -- {
  --   rw principal_action_class.smul_eq_iff_left _ tᵢ _ x₀,
  --   rw ring_sig_of_pas.vectorization_of_mem_support_keygen' x₀ H (ks.nth j) hkj,
  --   rw [← mul_inv, ← mul_inv],
  --   convert mul_inv_cancel_right (tᵢ * _) _,
  --   rw [inv_inv, mul_assoc, mul_comm, mul_comm (cs.nth i), ← mul_assoc],    
  -- },
  -- {
  --   exact rfl,
  -- }
end

end ring_sig_of_pas

variables {M : Type} {G X K : ℕ → Type}
variables [∀ n, fintype (G n)] [∀ n, fintype (X n)] 
variables [∀ n, inhabited (G n)] [∀ n, inhabited (X n)]
variables [decidable_eq M] [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)] [∀ n, decidable_eq (K n)]
variables [∀ n, comm_group (G n)] [∀ n, mul_action (G n) (X n)] [∀ n, principal_action_class (G n) (X n)]

/-- Construct a ring signature scheme from a hard homogenous space.
`x₀` is an arbitrary generator in `X` used as a base for the public keys.
Given security parameter `sp`, a signature on `n` parties is an element
  of type `K sp × vector (G sp) n × vector (G sp) n`.
The first element is the hash key used to sign this, and the two vectors are the signature
TODO: This should probably maybe a bunch of binds instead of let statemest? -/
def ring_signature_scheme_of_hhs [hard_homogeneous_space G X] 
  (x₀ : Π sp, X sp) (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp)) : 
  ring_signature_scheme M (λ sp n, K sp × vector (G sp) n × vector (G sp) n) X G :=
{
  rs := λ sp, ring_sig_of_pas (x₀ sp) (H.scheme sp),
  gen_poly_time := sorry,
  sign_poly_time := sorry,
  verify_poly_time := sorry,
}

variables [hard_homogeneous_space G X] 

theorem ring_signature_scheme_of_hhs.anonomyous (x₀ : Π sp, X sp) 
  (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp)) :
  (ring_signature_scheme_of_hhs x₀ H).anonomyous :=
begin
  sorry,
end

theorem ring_signature_scheme_of_hhs.unforgeable (x₀ : Π sp, X sp) 
  (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp)) :
  (ring_signature_scheme_of_hhs x₀ H).unforgeable :=
begin
  sorry,
end
