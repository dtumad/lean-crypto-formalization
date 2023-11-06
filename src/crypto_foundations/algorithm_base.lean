/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.identity_oracle
import crypto_constructions.hhs_signatures.commits

/-!
# Base Type for Algorithms

Testing out idea for `algorithm_base`
-/

open oracle_comp oracle_spec
open_locale ennreal

------------------------------------------------

structure algorithm_base (spec : oracle_spec) :=
(base_S : Type)
(base_so : sim_oracle spec uniform_selecting base_S)

def prob_comp' (α : Type) :=
oracle_comp uniform_selecting α

namespace algorithm_base

variables {spec : oracle_spec} {α β : Type}

def exec (alg : algorithm_base spec)
  (oa : oracle_comp spec α) : prob_comp' α :=
dsimulate' alg.base_so oa

end algorithm_base

--------------------------------------------------

structure asymm_enc_alg (spec : oracle_spec) (M PK SK C : Type)
  extends algorithm_base spec :=
(keygen : unit → oracle_comp spec (PK × SK))
(encrypt : M × PK → oracle_comp spec C)
(decrypt : C × SK → oracle_comp spec M)

example {spec : oracle_spec} {M PK SK C : Type}
  (asymm_enc : asymm_enc_alg spec M PK SK C) :
  prob_comp' (PK × SK) :=
asymm_enc.exec (asymm_enc.keygen ())

------------------------------------------------

structure sec_experiment (exp_spec : oracle_spec) (α β : Type)
  extends algorithm_base exp_spec :=
(inp_gen : oracle_comp exp_spec α)
(run : α → oracle_comp exp_spec β)
(is_valid : α × β → Prop)

namespace sec_experiment

variables {exp_spec : oracle_spec} {α β : Type}

def run_experiment (exp : sec_experiment exp_spec α β) :
  oracle_comp uniform_selecting (α × β)  :=
exp.exec (do
  { x ← exp.inp_gen,
    y ← exp.run x,
    return (x, y) })

noncomputable def advantage (exp : sec_experiment exp_spec α β) : ℝ≥0∞ :=
⁅exp.is_valid | exp.run_experiment⁆

end sec_experiment

------------------------------------------------

structure signature_alg (spec : oracle_spec)
  (M PK SK S : Type) extends algorithm_base spec :=
(keygen : unit → oracle_comp spec (PK × SK))
(sign : (PK × SK) × M → oracle_comp spec S)
(verify : PK × M × S → oracle_comp spec bool)

namespace signature_alg

variables {spec : oracle_spec} {M PK SK S : Type}

def soundness_experiment (sig : signature_alg spec M PK SK S) (m : M) :
  sec_experiment spec (PK × SK) bool :=
{ inp_gen := sig.keygen (),
  run := λ ⟨pk, sk⟩, do
    { σ ← sig.sign ((pk, sk), m),
      sig.verify (pk, m, σ) },
  is_valid := λ ⟨ks, b⟩, b = tt,
  .. sig } -- Includes `base_so`

-- Don't ever need to mention potential random oracles
def sound (sig : signature_alg spec M PK SK S) : Prop :=
∀ (m : M), (soundness_experiment sig m).advantage = 1

end signature_alg

noncomputable def hhs_signature (G X M : Type) [decidable_eq M]
  [add_comm_group G] [algorithmic_homogenous_space G X] (n : ℕ) :
  signature_alg (uniform_selecting ++ (vector X n × M ↦ₒ vector bool n))
    M (X × X) G (vector G n × vector bool n) :=
{ -- Choose a public key by picking a random base point `x₀` and secret key `sk` (`pk` is forced).
  keygen := λ u, do
    { x₀ ←$ᵗ X, sk ←$ᵗ G,
      return ((x₀, sk +ᵥ x₀), sk) },
  -- Sign a message by choosing `n` random commitments, and giving secret key proofs for each.
  sign := λ ⟨⟨⟨x₀, pk⟩, sk⟩, m⟩, do
    { (cs : vector G n) ← repeat ($ᵗ G) n,
      (ys : vector X n) ← return (cs.map (+ᵥ pk)),
      (hash : vector bool n) ← query₂ () (ys, m),
      return (zip_commits sk cs hash, hash) },
  -- Verify a signature by checking that the commitments map to the expected values.
  verify := λ ⟨⟨x₀, pk⟩, m, zs, hash⟩, do
    { (ys : vector X n) ← return (retrieve_commits x₀ pk zs hash),
      (hash' : vector bool n) ← query₂ () (ys, m),
      return (hash' = hash) },
  -- Right oracle should behave as a random oracle.
  base_so := idₛₒ ++ₛ randomₛₒ,
  .. } -- Infer `base_S`

