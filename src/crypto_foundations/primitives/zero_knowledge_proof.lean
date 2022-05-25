import computational_monads.asymptotics.polynomial_time
import data.list.basic

open_locale nnreal ennreal

open oracle_comp

/-- Zero knowledge proof for a language `L` with with a set of potential witnesses `W`.
  `is_witness` is an abstract specification of the witnesses for statements in the language -/
structure zero_knowledge_proof {L W : Type} 
  (is_witness : L → W → Prop) :=
(oracles : oracle_spec) -- Common random oracles for prove and verify
(oracles_finite_range : oracles.finite_range) 
(P : Type) -- The type of the resulting proof
(prove : L × W → oracle_comp oracles P) -- Construct a proof of `x : L` using a witness `w : W`
(verify : L × P → oracle_comp oracles bool) -- Verify a proof in `σ : P` of a statement in `x : L`
(prove_poly_time : poly_time_oracle_comp prove)
(verify_poly_time : poly_time_oracle_comp verify)

namespace zero_knowledge_proof

variables {L W : Type} {is_witness : L → W → Prop}
  (zkp : zero_knowledge_proof is_witness)

instance oracles_finite_range' : zkp.oracles.finite_range :=
zkp.oracles_finite_range

def completeness_experiment (statement : L) (witness : W) :
  oracle_comp zkp.oracles bool :=
(zkp.prove (statement, witness)) >>= (λ signature, zkp.verify (statement, signature))

-- TODO: the adversary should have access to a signing oracle
def signing_experiment (adversary : L × W → oracle_comp zkp.oracles zkp.P)
  (statement : L) (witness : W) :
  oracle_comp zkp.oracles bool :=
(adversary (statement, witness)) >>= (λ signature, zkp.verify (statement, signature))

/-- System is `ε`-complete if an honest prover always gets a valid proof except for probability `ε`.
  We represent this by doing the signing -/
def complete (ε : ℝ≥0) : Prop := 
∀ (statement : L) (witness : W) (h : is_witness statement witness),
  ⟦ (=) ff | signing_experiment zkp zkp.prove statement witness ⟧ ≤ ε

-- TODO: maybe should define `ε`-sound, and then soundness of the scheme is existence of negligible `ℕ` indexed `ε`?

end zero_knowledge_proof

section zero_knowledge_proof_scheme

open zero_knowledge_proof

variables {L W : ℕ → Type} (is_witness : Π (n : ℕ), L n → W n → Prop)

structure zero_knowledge_proof_scheme {L W : ℕ → Type} (is_witness : Π (n : ℕ), L n → W n → Prop) :=
(zkp (security_parameter : ℕ) : zero_knowledge_proof $ is_witness security_parameter)

/-- No poly-time adversary can sign a non-witness with better than `negligible` odds,
  as the security_parameter increases
  TODO: something about all this indexing seems off -/
def sound (zkps : zero_knowledge_proof_scheme is_witness): Prop :=
∀ (adversary : Π n, L n × W n → oracle_comp (zkps.zkp n).oracles (zkps.zkp n).P)
  (adversary_poly_time : Π n, poly_time_oracle_comp $ adversary n)
  (statement : Π n, L n) (witness : Π n, W n) (h : ∀ n, ¬ (is_witness n (statement n) (witness n))),
  negligable (λ n, ⟦ (=) tt | signing_experiment (zkps.zkp n) (adversary n) (statement n) (witness n) ⟧)

end zero_knowledge_proof_scheme

