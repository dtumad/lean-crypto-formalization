import crypto_foundations.dist_sem
import computational_complexity.complexity_class
import data.list.basic

/-!
# Ring Signatures

This file defines ring signatures and ring signature schemes, and their cryptographic properties.
The security properties `complete`, `anonomyous`, and `unforgeable` are defined in terms of corresponding experiments.
-/

section ring_signature

/-- Definition of a ring signature, all methods take a security parameter `sp` as input.
`gen` returns a public key and secret key
`sign` returns a signature on a message, where `i : fin n` is the signer's index in the `n`-person ring
  and the list of signers is given in the form of an `n` element vector,
`verify` checks whether a given signature is valid on a ring and a message
TODO: Double check the polynomial time stuff -/
structure ring_signature (M : Type) (S : ℕ → ℕ → Type) (PK SK : ℕ → Type) :=
(gen (sp : ℕ) : comp (PK sp × SK sp))
(gen_well_formed : ∀ sp, (gen sp).is_well_formed)
(gen_poly_time : poly_time_comp gen)
(sign (sp n : ℕ) (i : fin n) (sk : SK sp) : (vector (PK sp) n) × M → comp (S sp n))
(sign_well_formed : ∀ sp n i sk inp, (sign sp n i sk inp).is_well_formed)
(sign_poly_time : ∀ (n : ℕ) (i : fin n) (sk : Π sp, SK sp) (inp : Π sp, vector (PK sp) n × M), 
  poly_time_cost (λ sp, sign sp n i (sk sp)) ∧ poly_time_comp (λ sp, sign sp n i (sk sp) (inp sp)))
(verify (sp n : ℕ) : vector (PK sp) n × M × S sp n → bool)
(verify_poly_time : ∀ (n : ℕ), poly_time_cost (λ sp, verify sp n))

variables {M : Type} {PK SK : ℕ → Type} {S : ℕ → ℕ → Type} 
variables (rs : ring_signature M S PK SK) {sp : ℕ}

instance generate_keys_well_formed : (rs.gen sp).is_well_formed :=
rs.gen_well_formed sp

instance sign_well_formed (n : ℕ) (i : fin n) (sk : SK sp) (inp : vector (PK sp) n × M):
  (rs.sign sp n i sk inp).is_well_formed :=
rs.sign_well_formed sp n i sk inp 

def completeness_experiment (rs : ring_signature M S PK SK)
  (sp n : ℕ) (i : fin n) (sk : SK sp) (r : vector (PK sp) n) (m : M) : comp bool :=
comp.bind (rs.sign sp n i sk (r, m)) (λ s, comp.ret (rs.verify sp n (r, m, s)))

instance completeness_expiriement.is_well_formed (rs : ring_signature M S PK SK)
  (sp n : ℕ) (i : fin n) (sk : SK sp) (r : vector (PK sp) n) (m : M) : 
  (completeness_experiment rs sp n i sk r m).is_well_formed :=
begin
  unfold completeness_experiment,
  apply_instance,
end

/-- A ring signature is complete if for any list if completeness experiment always succeeds.
  Note that success is only required if the ring `r` consists of public keys in the support of `-/
def ring_signature.complete (rs : ring_signature M S PK SK) :=
∀ (sp n : ℕ) (i : fin n) (sk : SK sp) (r : vector (PK sp) n) (m : M) 
  (hsk : (r.nth i, sk) ∈ (rs.gen sp).support)
  (hr : ∀ (j : fin n), ∃ sk, (r.nth i, sk) ∈ (rs.gen sp).support), 
comp.Pr (completeness_experiment rs sp n i sk r m) = 1

-- TODO: rerwite these using the branch with oracle stuff
def ring_signature.anonomyous (rs : ring_signature M S PK SK) :=
false

def ring_signature.unforgeable (rs : ring_signature M S PK SK) :=
false

end ring_signature