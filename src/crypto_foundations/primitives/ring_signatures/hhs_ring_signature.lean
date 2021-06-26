import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import crypto_foundations.primitives.ring_signatures.ring_signature
import crypto_foundations.primitives.hash_function.hash_function

import data.vector2

/-!
# Hard Homogenous Space based Ring Signature Scheme

This file constructs a ring signature from a hard homogenous space.
Note that the construction requires a hash function into the group G.
-/

section ring_sig_of_pa

variables {M G X K : Type}
  [fintype G] [fintype X] 
  [inhabited G] [inhabited X] 
  [decidable_eq M] [decidable_eq X] [decidable_eq G] [decidable_eq K]
variables [group G] [mul_action G X]

def ring_sig_of_pas [principal_action_class G X]
  (x₀ : X) (H : hash_f K (list X × M) G) :
  ring_sig M (λ n, K × vector G n × vector G n) X G :=
{
  gen := comp.bind (comp.rnd (G)) 
    (λ g, comp.ret (g • x₀, g)),
  gen_well_formed := by apply_instance,
  sign := begin
    refine λ n i sk R m, _,
    refine (comp.rnd (G)).bind (λ t₁, _),
    refine (comp.rnd (vector (G) n)).bind (λ rs, _),
    refine (comp.rnd (vector (G) n)).bind (λ cs, _),
    let Ts : vector X n := vector.of_fn (λ j, (rs.nth j * cs.nth j) • R.nth j),
    let Tᵢ : X := t₁ • x₀,
    let Ts' : vector X n := vector.of_fn (λ j, if j = i then Tᵢ else Ts.nth j),
    let h : list X × M := ⟨vector.to_list (x₀ ::ᵥ (R.append Ts')), m⟩,
    refine (H.keygen).bind (λ k, _),
    let c : G := H.hash k h,
    let cᵢ : G := c * ((cs.map (λ g, g⁻¹)).to_list.prod),
    let rᵢ : G := t₁ * sk⁻¹ * cᵢ⁻¹,
    let cs' : vector (G) n := vector.of_fn (λ j, if j = i then cᵢ else cs.nth j),
    let rs' : vector (G) n := vector.of_fn (λ j, if j = i then rᵢ else rs.nth j),
    exact comp.ret (k, cs', rs'),
  end,
  sign_well_formed := by apply_instance,
  verify := begin
    intros n R m σ,
    let k : K := σ.1,
    let cs : vector (G) n := σ.2.1,
    let rs : vector (G) n := σ.2.2,
    let Ts : vector (X) n := vector.of_fn (λ j, (rs.nth j * cs.nth j) • R.nth j),
    let h : list (X) × M := ⟨vector.to_list (x₀ ::ᵥ (R.append Ts)), m⟩,
    exact H.hash k h = cs.to_list.prod,
  end,
}

theorem ring_sig_of_pas.complete [principal_action_class G X]
  (x₀ : X) (H : hash_f K (list X × M) G) :
  (ring_sig_of_pas x₀ H).complete :=
begin
  intros n i m,
  unfold comp.Pr,
  rw comp.Pr_prop_eq_one_iff,
  intros b hb,
  squeeze_simp [ring_sig.completeness_experiment] at hb,
  sorry,
end

end ring_sig_of_pa

variables {M : Type} {S G X K : ℕ → Type}
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
