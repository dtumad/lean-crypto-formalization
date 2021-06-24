import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import crypto_foundations.primitives.ring_signatures.ring_signature
import crypto_foundations.primitives.hash_function.hash_function

import data.vector2

/-!
# Hard Homogenous Space based Ring Signature Scheme

This file constructs a ring signature from a hard homogenous space.
Note that the construction requires a hash function into the group G.

-/

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
def ring_signature_of_hhs [hard_homogeneous_space G X] 
  (x₀ : Π sp, X sp) (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp)) : 
  ring_signature M (λ sp n, K sp × vector (G sp) n × vector (G sp) n) X G :=
{
  gen := λ sp, comp.bind (comp.rnd (G sp)) 
    (λ g, comp.ret (g • (x₀ sp), g)),
  gen_well_formed := by apply_instance,
  gen_poly_time := begin
    sorry,
  end,
  sign := begin
    intros sp n i sk inp,
    refine (comp.rnd (G sp)).bind (λ t₁, _),
    refine (comp.rnd (vector (G sp) n)).bind (λ rs, _),
    refine (comp.rnd (vector (G sp) n)).bind (λ cs, _),
    let R := inp.1,
    let m := inp.2,
    let Ts : vector (X sp) n := vector.of_fn (λ j, (rs.nth j * cs.nth j) • R.nth j),
    let Tᵢ : X sp := t₁ • (x₀ sp),
    let Ts' : vector (X sp) n := vector.of_fn (λ j, if j = i then Tᵢ else Ts.nth j),
    let h : list (X sp) × M := ⟨vector.to_list ((x₀ sp) ::ᵥ (R.append Ts')), m⟩,
    refine (H.keygen sp).bind (λ k, _),
    let c : G sp := H.hash k h,
    let cᵢ : G sp := c * ((cs.map (λ g, g⁻¹)).to_list.prod),
    let rᵢ : G sp := t₁ * sk⁻¹ * cᵢ⁻¹,
    let cs' : vector (G sp) n := vector.of_fn (λ j, if j = i then cᵢ else cs.nth j),
    let rs' : vector (G sp) n := vector.of_fn (λ j, if j = i then rᵢ else rs.nth j),
    exact comp.ret (k, cs', rs'),
  end,
  sign_well_formed := sorry,
  sign_poly_time := sorry,
  verify := begin
    intros sp n inp,
    let R : vector (X sp) n := inp.1,
    let m : M := inp.2.1,
    let k : K sp := inp.2.2.1,
    let cs : vector (G sp) n := inp.2.2.2.1,
    let rs : vector (G sp) n := inp.2.2.2.2,
    let Ts : vector (X sp) n := vector.of_fn (λ j, (rs.nth j * cs.nth j) • R.nth j),
    let h : list (X sp) × M := ⟨vector.to_list ((x₀ sp) ::ᵥ (R.append Ts)), m⟩,
    exact H.hash k h = cs.to_list.prod,
  end,
  verify_poly_time := sorry,
}

namespace ring_signature_of_hard_homogenous_space

variables [hard_homogeneous_space G X] 
  (x₀ : Π sp, X sp) (H : hash_scheme K (λ sp, list (X sp) × M) (λ sp, G sp))

@[simp]
lemma verify_apply {sp n : ℕ} (R : vector (X sp) n)
  (m : M) (k : K sp) (cs rs : vector (G sp) n) : 
  (ring_signature_of_hhs x₀ H).verify sp n (R, m, k, cs, rs) = 
    (H.hash k ⟨vector.to_list ((x₀ sp) ::ᵥ (R.append (vector.of_fn (λ j, (rs.nth j * cs.nth j) • R.nth j)))), m⟩ = cs.to_list.prod) :=
rfl

@[simp] 
lemma mem_support_gen_iff {sp : ℕ} (pk : X sp) (sk : G sp) :
  (pk, sk) ∈ ((ring_signature_of_hhs x₀ H).gen sp).support ↔
    pk = sk • (x₀ sp) :=
begin
  erw comp.mem_support_bind_rnd,
  simp,
end

theorem hhs_ring_signature_complete :
  (ring_signature_of_hhs x₀ H).complete :=
begin
  intros sp n i m,
  unfold comp.Pr,
  rw comp.Pr_prop_eq_one_iff,
  intros b hb,
  simp [ring_signature.completeness_experiment] at hb,
  sorry,
end

end ring_signature_of_hard_homogenous_space