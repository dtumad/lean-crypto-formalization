import crypto_foundations.primitives.signature.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import data.vector2


variables (M G X : Type)
  [fintype G] [fintype X] [inhabited G] [inhabited X] 
  [decidable_eq M] [decidable_eq G] [decidable_eq X]
variables [add_comm_group G] [add_action G X]
variables [function_cost_model ℚ] [comp_cost_model ℚ]

variable [principal_action_class G X]

open oracle_comp

/-- `x₀` is a base point to use for public keys, analogous to a fixed generator of a cyclic group.
  `t` is the number of repetitions of the proof, higher values increase the soundness of the system. -/
def signature_of_principal_action_class (x₀ : X) (t : ℕ) : 
  signature M X G (vector (G × bool) t)
  -- Input and output types for random oracle used to model a hash function
    (list X × M) (vector bool t) :=
{ 
  gen := λ _, do
  { sk ← comp.rnd G,
    return (sk +ᵥ x₀, sk) },
  sign := λ inp, do
  { (pk, sk, m) ← return inp,
    -- Choose `t` values from `G` at random
    cs ← oc_ret (comp.vector_call (comp.rnd G) t),
    ys ← return (cs.map (λ c, c +ᵥ pk)),
    -- Query the random oracle on `ys`
    (h : vector bool t) ← oc_query () (ys.to_list, m),
    return (vector.zip_with cs h 
      (λ c b, (if b then c else c + sk, b))) },
  verify := λ inp, do
  { (pk, m, σ) ← return inp,
    -- This should be the same `ys` value for honest signatures
    ys ← return (σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀)),
    (h : vector bool t) ← oc_query () (ys.to_list, m),
    return (h = σ.map prod.snd) } 
}

instance signature_of_principal_action_class.is_well_formed (x₀ : X) (t : ℕ) :
  (signature_of_principal_action_class M G X x₀ t).is_well_formed :=
{ gen_is_well_formed := by simp [signature_of_principal_action_class],
  sign_is_well_formed := by simp [signature_of_principal_action_class],
  verify_is_well_formed := by simp [signature_of_principal_action_class] }

namespace signature_of_principal_action_class

theorem complete (x₀ : X) (t : ℕ) :
  (signature_of_principal_action_class M G X x₀ t).complete :=
begin
  intro m,
  rw [comp.Pr_def, comp.Pr_prop_eq_one_iff],
  simp only [signature.mem_completeness_experiment_iff],
  rintro a ⟨pk, sk, hks, σ, log, hσ, b', log', hb', h⟩,
  sorry,
end

end signature_of_principal_action_class