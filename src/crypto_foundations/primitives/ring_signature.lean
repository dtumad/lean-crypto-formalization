import crypto_foundations.dist_sem
import data.list.basic

/-- `M` is the message space of the ring signature
  `S` is the signature space of the ring signature -/
variables (M S : Type) {n : ℕ}

structure ring_signature (PK SK : Type) :=
-- Generate a pair of a public key and a secret key
(generate_keys : comp (PK × SK))
-- Signature on the input `(secret_key, message, ring, user)`
(sign : SK × M × (list PK) × ℕ → S)
-- Verification of an input of the form `(message, ring, signature)`
(verify : M × (list PK) × S → bool)
(completeness (sk : SK) (m : M) (r : list PK) (n : ℕ)
  (h : (sorry, sk) ∈ generate_keys.support): 
  verify (m, r, sign (sk, m, r, n)) = tt)

/-- A `ring_signature_scheme` is a set of of `ring_signatures` parameterized
  by some security parameter `k`-/
def ring_signature_scheme (PK SK : ℕ → Type) := 
∀ k, ring_signature M S (PK k) (SK k)