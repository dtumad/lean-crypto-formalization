import computational_monads.probabalistic_computation.forking_lemma
import computational_complexity.complexity_class
import data.list.basic

open_locale nnreal ennreal

open prob_comp oracle_comp

/-- Zero knowledge proof for a language `L` with with a set of potential witnesses `W`.
  `is_witness` is an abstract specification of the witnesses for statements in the language -/
structure zero_knowledge_proof {L W : Type} 
  (is_witness : L → W → Prop) :=
(random_oracles : oracle_comp_spec) -- Common random oracles for prove and verify
(P : Type) -- The type of the resulting proof
(prove : L × W → oracle_comp random_oracles P) -- Construct a proof of `x : L` using a witness `w : W`
(verify : L × P → oracle_comp random_oracles bool) -- Verify a proof in `σ : P` of a statement in `x : L`
(prove_poly_time : oracle_poly_time prove)
(verify_poly_time : oracle_poly_time verify)

namespace zero_knowledge_proof

variables {L W : Type} {is_witness : L → W → Prop}
  (zkp : zero_knowledge_proof is_witness)

/-- System is `ε`-complete if an honest prover gets a valid proof with probability at least `ε`-/
def complete [zkp.random_oracles.finite] (ε : ℝ≥0) : Prop := 
∀ (statement : L) (witness : W) (h : is_witness statement witness),
(simulate_result (random_oracle' zkp.random_oracles) (query_log.nil zkp.random_oracles) (do {
  proof ← zkp.prove (statement, witness),
  zkp.verify (statement, proof)
})).prob_success ≥ ε

/-- System is `ε`-sound if no polynomial time adversary can generate a proof for a non-witness,
  except with probability at most `ε` (given access to the same shared random oracles)-/
def sound [zkp.random_oracles.finite] (ε : ℝ≥0) : Prop :=
∀ (language : L) (witness : W) (h : ¬ is_witness language witness)
  (adv : L × W → oracle_comp zkp.random_oracles zkp.P)
  (hadv : oracle_poly_time adv),
(simulate_result (random_oracle' zkp.random_oracles) (query_log.nil zkp.random_oracles) (do {
  proof ← adv (language, witness),
  zkp.verify (language, proof)
})).prob_success ≤ ε

end zero_knowledge_proof
