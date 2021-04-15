import crypto_foundations.dist_sem
import data.list.basic

/-- `M` is the message space of the ring signature
  `S` is the signature space of the ring signature -/
variables {n : ℕ}

structure ring_signature (M S PK SK : Type) :=
-- Generate a pair of a public key and a secret key
(generate_keys : comp (PK × SK))
(generate_keys_well_formed : generate_keys.well_formed_comp)
-- Signature on the input `(secret_key, message, user, remaining ring of users)`
(sign : SK × M × PK × (list PK) → comp S)
(sign_well_formed : ∀ sk m pk r, (sign (sk, m, pk, r)).well_formed_comp)
-- Verification of an input of the form `(message, ring, signature)`
(verify : M × (list PK) × S → bool)

variables {M S PK SK : Type} (rs : ring_signature M S PK SK)

@[simp] lemma generate_keys_well_formed : rs.generate_keys.well_formed_comp :=
rs.generate_keys_well_formed

@[simp] lemma sign_well_formed {sk : SK} {m : M} {pk : PK} {r : list PK} :
  (rs.sign (sk, m, pk, r)).well_formed_comp :=
rs.sign_well_formed sk m pk r

def completeness_experiment (rs : ring_signature M S PK SK)
  (sk : SK) (m : M) (pk : PK) (r : list PK) : comp bool :=
comp.bind (rs.sign (sk, m, pk, r)) (λ s,
comp.ret (rs.verify (m, r, s)))

@[simp] lemma well_formed_comp_completeness_expiriement {rs : ring_signature M S PK SK}
  {sk : SK} {m : M} {pk : PK} {r : list PK} :
  (completeness_experiment rs sk m pk r).well_formed_comp :=
by simp [completeness_experiment]

def ring_signature.complete (rs : ring_signature M S PK SK) :=
∀ sk m pk r, comp.Pr (completeness_experiment rs sk m pk r) (by simp) = 1

/-- A `ring_signature_scheme` is a set of of `ring_signatures` parameterized
  by some security parameter `k`-/
def ring_signature_scheme (PK SK : ℕ → Type) := 
∀ k, ring_signature M S (PK k) (SK k)