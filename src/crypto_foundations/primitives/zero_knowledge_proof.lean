import computational_monads.probabalistic_computation.forking_lemma
import computational_complexity.complexity_class
import data.list.basic

open_locale nnreal ennreal

open prob_comp oracle_comp

/-- Proof of knowledge of a witness `w : W` for a statement `x : L` in language `L` -/
structure zero_knowledge_proof 
  {L W : Type} (is_witness : L → W → Prop) (S U V : Type) :=
(prove : L × W → oracle_comp ⟦U →ᵒ V⟧ S)
(verify : L × S → oracle_comp ⟦U →ᵒ V⟧ bool)

variables {L W S U V : Type} (is_witness : L → W → Prop)
  [decidable_eq U] [fintype V] [nonempty V]

/-- `ε` is the strength of the proof -/
def complete (zkp : zero_knowledge_proof is_witness S U V)
  (ε : ℝ≥0) : Prop :=
∀ (language : L) (witness : W) (h : is_witness language witness), 
(simulate_result (random_oracle U V) [] (do {
  proof ← zkp.prove (language, witness),
  zkp.verify (language, proof)
})).prob_success ≥ 0.5 + ε

def sound (zkp : zero_knowledge_proof is_witness S U V)
  (ε : ℝ≥0) : Prop :=
∀ (language : L) (witness : W) (h : ¬ is_witness language witness)
  (adv : L × W → oracle_comp ⟦U →ᵒ V⟧ S),
(simulate_result (random_oracle U V) [] (do {
  proof ← adv (language, witness),
  zkp.verify (language, proof)
})).prob_success ≤ 0.5 - ε

