import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import crypto_foundations.primitives.ring_signatures.ring_signature

/-!
# Hard Homogenous Space based Ring Signature Scheme
-/

variables (G X : ℕ → Type) [∀ n, fintype (G n)] [∀ n, fintype (X n)]
  [∀ n, inhabited (X n)] [∀ n, decidable_eq (G n)] [∀ n, decidable_eq (X n)] 
  [∀ n, homogeneous_space (G n) (X n)]

variables (M S : Type)

/-- Construct a ring signature scheme from a hard homogenous space.
`x₀` is an arbitrary generator in `X` used as a base for the public keys.
TODO: clean this up so the simplifier can properly reduce things -/
def hhs_ring_signature [hard_homogeneous_space G X] (x₀ : ∀ n, X n) : 
  ring_signature_scheme M S G X :=
λ n, {
  generate_keys := comp.bind (comp.rnd (G n)) 
    (λ g, comp.ret (g, g • x₀ n)),
  generate_keys_well_formed := by simp,
  sign := sorry,
  sign_well_formed := sorry,
  verify := sorry
}

lemma hhs_ring_signature_complete [hard_homogeneous_space G X] (x₀ : ∀ n, X n) :
  (hhs_ring_signature G X M S x₀).complete :=
sorry
