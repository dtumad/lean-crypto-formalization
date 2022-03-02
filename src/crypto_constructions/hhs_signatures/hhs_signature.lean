import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import data.vector.zip


variables (M G X : Type)
  [fintype G] [fintype X] [inhabited G] [inhabited X] 
  [decidable_eq M] [decidable_eq G] [decidable_eq X]
variables [add_comm_group G] [add_action G X]
variables [function_cost_model ℚ] [comp_cost_model ℚ] 

open prob_comp oracle_comp

/-- `x₀` is a base point to use for public keys, analogous to a fixed generator of a cyclic group.
  `t` is the number of repetitions of the proof, higher values increase the soundness of the system. -/
noncomputable def signature_of_principal_action_class 
  [principal_action_class G X] (x₀ : X) (t : ℕ) : 
  signature ⟦list X × M →ᵒ vector bool t⟧ M X G (vector (G × bool) t) :=
{ 
  gen := λ _, do
  { sk ← sample ($ᵗ G),
    return (sk +ᵥ x₀, sk) },
  sign := λ inp, do
  { (pk, sk, m) ← return inp,
    -- Choose `t` values from `G` at random
    cs ← sample (vector_call ($ᵗ G) t),
    -- Mask each random value with a public key
    ys ← return (cs.map (λ c, c +ᵥ pk)),
    -- Query the random oracle on `ys` and `m` to get a bitstring of length `t`
    (h : vector bool t) ← query () (ys.to_list, m),
    -- Further mask the indexes which are `1` in the hash with the secret key
    return (vector.zip_with (λ c (b : bool), (if b then c else c + sk, b)) cs h) },
  verify := λ inp, do
  { (pk, m, σ) ← return inp,
    -- This should be the same `ys` value for honest signatures
    ys ← return (σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀)),
    (h : vector bool t) ← query () (ys.to_list, m),
    -- Check that the hash matches the bitstring given by the signer
    return (h = σ.map prod.snd) } 
}

variable [principal_action_class G X]

namespace signature_of_principal_action_class

variables (x₀ : X) (t : ℕ)

-- @[simp]
-- lemma mem_support_gen_iff (u : unit) (ks : X × G) :
--   ks ∈ ((signature_of_principal_action_class M G X x₀ t).gen u).alg.support ↔
--     ks.fst = ks.snd +ᵥ x₀ :=
-- begin
--   simp [signature_of_principal_action_class],

--   refine ⟨λ h, _, λ h, ⟨ks.snd, prod.ext h.symm rfl⟩⟩,
--   obtain ⟨i, hi⟩ := h,
--   simp [hi.symm],
-- end

theorem complete (x₀ : X) (t : ℕ) :
  (signature_of_principal_action_class M G X x₀ t).complete :=
begin
  intro m, sorry
  -- rw [comp.Pr_def, comp.Pr_prop_eq_one_iff],
  -- simp only [signature.mem_completeness_experiment_iff],
  -- rintro a ⟨pk, sk, hks, σ, log, hσ, b', log', hb', h⟩,
  -- simp [mem_support_gen_iff] at hks,
  -- sorry,
end

end signature_of_principal_action_class