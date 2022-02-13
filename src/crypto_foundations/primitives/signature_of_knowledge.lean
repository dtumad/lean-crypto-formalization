import computational_monads.probabalistic_computation.forking_lemma
import computational_complexity.complexity_class
import data.list.basic

import crypto_foundations.hardness_assumptions.hard_homogeneous_space

open_locale nnreal ennreal

open prob_comp oracle_comp

-- M - message; L - Language; W - Witness; S - Signature
structure signature_of_knowledge (oracle_access : oracle_comp_spec)
  {L W : Type} (is_witness : L → W → Prop) (M S : Type) :=
(sign (inp : M × L × W) : oracle_comp oracle_access S)
(verify (inp : M × L × S) : oracle_comp oracle_access bool)

namespace signature_of_knowledge

variables {oracle_access : oracle_comp_spec}
  {L W : Type} {is_witness : L → W → Prop} {M S : Type}
  (sok : signature_of_knowledge oracle_access is_witness M S)

def completeness_experiment (so : simulation_oracle oracle_access) (s : so.S)
  (m : M) (stmt : L) (witness : W) : prob_comp bool :=
simulate_result so s (do {
  σ ← sok.sign (m, stmt, witness),
  sok.verify (m, stmt, σ) })

def complete (so : simulation_oracle oracle_access) (s : so.S) : Prop :=
∀ (m : M) (statement : L) (witness : W), is_witness statement witness →
  (completeness_experiment sok so s m statement witness).prob_success = 1

-- TODO: integrate this
def signing_oracle (M S : Type) : oracle_comp_spec :=
singleton_spec M S

def unforgeable_experiment (so : simulation_oracle (oracle_access ++ signing_oracle M S)) (s : so.S)
  (A : L → oracle_comp (oracle_access ++ signing_oracle M S) (M × S))
  (stmt : L) : prob_comp bool :=
sorry -- TODO: need to jump between oracle accesses for this

end signature_of_knowledge

variables (M G X : Type)
  [fintype G] [fintype X] [inhabited G] [inhabited X] 
  [decidable_eq M] [decidable_eq G] [decidable_eq X]
variables [add_comm_group G] [add_action G X]
variables [function_cost_model ℚ] [comp_cost_model ℚ] 

-- Proof of knowledge of the discrete log (wrt `x₀`) of `x`
-- Language := point in `X`, Witness := discrete log wrt `x₀`
-- Verification of language membership by checking 
@[simps]
def hhs_sigk [principal_action_class G X] : 
  signature_of_knowledge (singleton_spec (M × X) bool) 
    (λ (x : X × X) (g : G), x.2 = g +ᵥ x.1) M (G × bool) :=
{ 
  sign := λ inp, do{
    (m, (x₀, x), g) ← return inp,
    g' ← sample (random G),
    y ← return (g' +ᵥ x),
    (b : bool) ← query () (m, y),
    return (if b then g' else g' + g, b)
  },
  verify := λ inp, do{
    (m, (x₀, x), c, b) ← return inp,
    -- This recovers `y = (g' + g) +ᵥ x₀` for an honest signer
    y ← return (if b then c +ᵥ x else c +ᵥ x₀),
    (b' : bool) ← query () (m, y),
    return (b = b')
  }
}

-- TODO: will need an additional oracle in `A` but probably not the result.
-- More general simulation by reducing between oracle_spec
def forkable_vec_adv_of_hhs_sigk_adv
  (A : X × X → oracle_comp (singleton_spec (M × X) bool) (M × (G × bool))) :
  X × X → sorry := sorry

def vec_adv_of_hhs_sigk_adv
  (A : X × X → oracle_comp (singleton_spec (M × X) bool) (M × (G × bool))) :
  X × X → prob_comp G :=
sorry



theorem thing [principal_action_class G X] :
  (hhs_sigk M G X).complete (random_oracle (M × X) bool) [] :=
begin
  rintros m ⟨x₀, x⟩ g hg,
  rw [prob_success, prob_event_eq_one_iff],
  rw [signature_of_knowledge.completeness_experiment],
  rw [simulate_result],
  rw [simulate_bind],
  simp only [functor.map],
  rw [support_bind_on_support],
  simp_rw [set.Union_subset_iff],
  rintros ⟨b, log⟩ hb,
  suffices : b = tt, by simpa,
  simp_rw [support_bind, set.mem_Union] at hb,
  obtain ⟨⟨⟨g', b'⟩, log'⟩, hg', h⟩ := hb,
  simp [hhs_sigk._match_2, random_oracle._match_1] at hg',
  sorry,
end