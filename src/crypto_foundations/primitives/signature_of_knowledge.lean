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

/-- Perfect completeness: not failing even negligibly often -/
def complete (so : simulation_oracle oracle_access) (s : so.S) : Prop :=
∀ (m : M) (statement : L) (witness : W), is_witness statement witness →
  (completeness_experiment sok so s m statement witness).prob_success = 1

-- /-- Simsetup generates a trapdoor for simsign to use -/
-- def simulatability_experiment (so : simulation_oracle oracle_access) (s : so.S)
--   {T : Type} (sim_setup : oracle_comp oracle_access T)
--   (sim_sign )
--   (adv : oracle_comp (oracle_access ++ ⟦M × L × W →ᵒ S⟧) bool) :=
-- do {

-- }

-- TODO: integrate this
def signing_oracle (M S : Type) [decidable_eq M] [nonempty S] : oracle_comp_spec :=
⟦M →ᵒ S⟧

-- def unforgeable_experiment (so : simulation_oracle (oracle_access ++ signing_oracle M S)) (s : so.S)
--   (A : L → oracle_comp (oracle_access ++ signing_oracle M S) (M × S))
--   (stmt : L) : prob_comp bool :=
-- simulate_result so s (do {
--   (m, σ) ← A stmt,
--   sok.verify (m, stmt, σ)
-- })

-- def unforgeable (so : simulation_oracle oracle_access) (s : so.S) : Prop :=
-- ∀ 

end signature_of_knowledge

variables (M G X : Type)
  [fintype G] [fintype X] [inhabited G] [inhabited X] 
  [decidable_eq M] [decidable_eq G] [decidable_eq X]
variables [add_comm_group G] [add_action G X]
variables [function_cost_model ℚ] [comp_cost_model ℚ] 

-- Proof of knowledge of the discrete log (wrt `x₀`) of `x`
-- Language := point in `X`, Witness := discrete log wrt `x₀`
-- Verification of language membership by checking
-- Needs access to a random oracle on `M × X` outputting a single bit

-- TODO: Random sampling of an element of `G` makes this noncomputable (could add something `- ≃ᵖ $ᵗ G` in HHS definition)
@[simps]
noncomputable def hhs_sigk [principal_action_class G X] (x₀ : X) : 
  signature_of_knowledge ⟦M × X →ᵒ bool⟧ 
    (λ (x : X) (g : G), x = g +ᵥ x₀) M (G × bool) :=
{ 
  sign := λ inp, do{
    (m, x, g) ← return inp,
    g' ← sample ($ᵗ G),
    y ← return (g' +ᵥ x),
    (b : bool) ← query () (m, y),
    return (if b then g' else g' + g, b)
  },
  verify := λ inp, do{
    (m, x, c, b) ← return inp,
    -- This recovers `y = (g' + g) +ᵥ x₀` for an honest signer
    y ← return (if b then c +ᵥ x else c +ᵥ x₀),
    (b' : bool) ← query () (m, y),
    return (b = b')
  }
}

-- TODO: will need an additional oracle in `A` but probably not the result.
-- More general simulation by reducing between oracle_spec
def forkable_vec_adv_of_hhs_sigk_adv
  (A : X × X → oracle_comp ⟦M × X →ᵒ bool⟧ (M × (G × bool))) :
  X × X → sorry := sorry

def vec_adv_of_hhs_sigk_adv
  (A : X × X → oracle_comp ⟦M × X →ᵒ bool⟧ (M × (G × bool))) :
  X × X → prob_comp G :=
sorry

theorem thing [principal_action_class G X] (x₀ : X) :
  (hhs_sigk M G X x₀).complete (random_oracle (M × X) bool) [] :=
begin
  rintros m x g hg,
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