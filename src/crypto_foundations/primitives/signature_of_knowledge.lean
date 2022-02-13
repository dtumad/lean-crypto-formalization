import computational_monads.probabalistic_computation.constructions
import computational_complexity.complexity_class
import data.list.basic

import crypto_foundations.hardness_assumptions.hard_homogeneous_space


open prob_comp oracle_comp

-- M - message; P - Statement; W - Witness; S - Signature
structure signature_of_knowledge (oracle_access : oracle_comp_spec)
  (M P W S : Type) (valid : P → W → Prop) :=
(sign (inp : M × P × W) : oracle_comp oracle_access S)
(verify (inp : M × P × S) : oracle_comp oracle_access bool)

namespace signature_of_knowledge

variables {oracle_access : oracle_comp_spec}
  {M P W S : Type} (valid : P → W → Prop)
  (sok : signature_of_knowledge oracle_access M P W S valid)

def completeness_experiment (so : simulation_oracle oracle_access)
  (s : so.S) (m : M) (p : P) (w : W) : prob_comp bool :=
(do{
  σ ← sok.sign (m, p, w),
  sok.verify (m, p, σ)
}).simulate_result so s

def complete (so : simulation_oracle oracle_access) (s : so.S) : Prop :=
∀ (m : M) (p : P) (w : W), valid p w →
  (completeness_experiment valid sok so s m p w).prob_success = 1


end signature_of_knowledge

variables (M G X : Type)
  [fintype G] [fintype X] [inhabited G] [inhabited X] 
  [decidable_eq M] [decidable_eq G] [decidable_eq X]
variables [add_comm_group G] [add_action G X]
variables [function_cost_model ℚ] [comp_cost_model ℚ] 

-- Proof of knowledge of the discrete log (wrt `x₀`) of `x`
def signature_of_discrete_log_principal_action_class 
  [principal_action_class G X] (x₀ : X) : 
  signature_of_knowledge (singleton_spec (X × M) bool) 
    M X G (G × bool) (λ x g, x = g +ᵥ x₀) :=
{ 
  sign := λ inp, do{
    (m, x, g) ← return inp,
    c ← sample (random G),
    y ← return (c +ᵥ x),
    (b : bool) ← query () (y, m),
    return (if b then c else c + g, b)
  },
  verify := λ inp, do{
    (m, x, c, b) ← return inp,
    -- This should recover `y` for an honest signer
    y ← return (if b then c +ᵥ x else c +ᵥ x₀),
    (b' : bool) ← query () (y, m),
    return (b = b')
  }
}