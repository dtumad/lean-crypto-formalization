import crypto_foundations.dist_sem
import data.list.basic

/-!
# Ring Signatures

This file defines ring signatures and ring signature schemes, and their cryptographic properties.
-/

section ring_signature

/-- Definition of a -/
structure ring_signature (M S PK SK : Type) :=
-- Generate a pair of a public key and a secret key
(generate_keys : comp (PK × SK))
(generate_keys_well_formed : generate_keys.is_well_formed)
-- Signature on the input `(secret_key, message, user, remaining ring of users)`
(sign : SK × M × PK × (list PK) → comp S)
(sign_well_formed : ∀ sk m pk r, (sign (sk, m, pk, r)).is_well_formed)
-- Verification of an input of the form `(message, ring, signature)`
(verify : M × (list PK) × S → bool)

variables {M S PK SK : Type} (rs : ring_signature M S PK SK)

instance generate_keys_well_formed : rs.generate_keys.is_well_formed :=
rs.generate_keys_well_formed

instance sign_well_formed {sk : SK} {m : M} {pk : PK} {r : list PK} :
  (rs.sign (sk, m, pk, r)).is_well_formed :=
rs.sign_well_formed sk m pk r

def completeness_experiment (rs : ring_signature M S PK SK)
  (m : M) (r : list PK) : comp bool :=
comp.bind (rs.generate_keys) (λ k, 
comp.bind (rs.sign (k.2, m, k.1, r)) (λ s,
comp.ret (rs.verify (m, r, s))))

instance ompleteness_expiriement.is_well_formed {rs : ring_signature M S PK SK}
  {m : M} {r : list PK} : (completeness_experiment rs m r).is_well_formed :=
begin
  unfold completeness_experiment,
  apply_instance,
end

def ring_signature.complete (rs : ring_signature M S PK SK) :=
∀ m r, comp.Pr (completeness_experiment rs m r) = 1

end ring_signature

section ring_signature_scheme

/-- A `ring_signature_scheme` is a set of of `ring_signatures` parameterized
  by some security parameter `k`-/
def ring_signature_scheme (M S : Type) (PK SK : ℕ → Type) := 
Π n, ring_signature M S (PK n) (SK n)

variables {M S : Type} {PK SK : ℕ → Type}

def ring_signature_scheme.complete (rss : ring_signature_scheme M S PK SK) :=
∀ n, (rss n).complete

end ring_signature_scheme