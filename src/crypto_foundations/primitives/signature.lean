import computational_monads.asymptotics.polynomial_time
import computational_monads.constructions.forking_lemma
import data.list.basic

/-!
# Cryptographic Signature Schemes

This file defines signature algorithms and security properties for them.

Note that the schemes assume algorithms have access to a shared random oracle.
Signature schemes that don't need this can assume a random oracle like `⊥ → ()`, 
  which won't actually be query-able since `⊥` is an uninhabited type
-/

open oracle_comp oracle_spec

/-- Signature on messages `M`, public and secret keys `PK` and `SK`, signatures of type `S`. 
  `oracle_access` specifies the oracles the algorithm can make use of  -/
structure signature (M PK SK S : Type) :=
(oracles : oracle_spec) (oracles_finite_range : oracles.finite_range)
(gen : unit → oracle_comp oracles (PK × SK))
(sign : PK × SK × M → oracle_comp oracles S)
(verify : PK × M × S → oracle_comp oracles bool)
(gen_poly_time : poly_time_oracle_comp gen)
(sign_poly_time : poly_time_oracle_comp sign)
(verify_poly_time : poly_time_oracle_comp verify)

namespace signature

variables {M PK SK S : Type}

/-- Add the `finite_range` to global type-class instances -/
instance oracles.finite_range (sig : signature M PK SK S) :
  sig.oracles.finite_range :=
sig.oracles_finite_range

section complete

/-- Generate a key, sign on the given message, and return the result of verify on the signature -/
def completeness_experiment (sig : signature M PK SK S) (m : M) :
  oracle_comp sig.oracles bool :=
do { 
  (pk, sk) ← sig.gen (),
  σ ← sig.sign (pk, sk, m),
  sig.verify (pk, m, σ) 
}

/-- Honest signer always generates a valid message. 
  TODO: could account for negligible failure rate? -/
def complete (sig : signature M PK SK S):=
∀ (m : M), ⟦ (=) tt | completeness_experiment sig m ⟧ = 1

end complete

section unforgeable

variables [inhabited S] [decidable_eq M] [decidable_eq S]

structure unforgeable_adversary (sig : signature M PK SK S) :=
(adv : PK → oracle_comp (sig.oracles ++ (M →ₒ S)) (M × S))
(adv_poly_time : poly_time_oracle_comp adv)

def simulate_sign (sig : signature M PK SK S) (pk : PK) (sk : SK) :
  simulation_oracle (sig.oracles ++ (M →ₒ S)) (sig.oracles) :=
identity_oracle sig.oracles ⟪++⟫ (⟪λ _ m, sig.sign (pk, sk, m)⟫ ∘ₛ (logging_simulation_oracle (M →ₒ S)))

def simulate_adversary (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) (pk : PK) (sk : SK) :
  oracle_comp sig.oracles (M × S × query_log (M →ₒ S)) :=
do {
  ((m, s), (), log, ()) ← (simulate (simulate_sign sig pk sk) (adversary.adv pk) ((), query_log.init _, ())),
  return (m, s, log)
}

def unforgeable_experiment (sig : signature M PK SK S)
  (adversary : unforgeable_adversary sig) :
  oracle_comp sig.oracles bool :=
do {
  (pk, sk) ← sig.gen (),
  (m, σ, log) ← simulate_adversary sig adversary pk sk,
  b ← sig.verify (pk, m, σ),
  return (b ∧ log.not_queried () m)
}

end unforgeable

end signature

/-- signature algorithms indexed by a security parameter -/
def signature_scheme (M PK SK S : ℕ → Type) :=
Π (sp : ℕ), signature (M sp) (PK sp) (SK sp) (S sp)

namespace signature_scheme

open signature

variables {M PK SK S : ℕ → Type}
  [∀ sp, inhabited $ S sp] [∀ sp, decidable_eq $ M sp] [∀ sp, decidable_eq $ S sp]

/-- Polynomial time adversary has negligible advantage in
  `unforgeable_experiment` as security parameter grows -/
def unforgeable (sig_scheme : signature_scheme M PK SK S) : Prop :=
∀ (adversary : Π (sp : ℕ), unforgeable_adversary $ sig_scheme sp),
  negligable (λ sp, ⟦ (=) tt | unforgeable_experiment (sig_scheme sp) (adversary sp)⟧)

end signature_scheme