import crypto_foundations.primitives.signature
import crypto_foundations.hardness_assumptions.hard_homogeneous_space
import computational_monads.constructions.vector_call
import data.vector.zip

open oracle_comp oracle_spec

variables (G X M : Type) [fintype G] [fintype X] [inhabited X] [inhabited G]
  [decidable_eq G] [decidable_eq X] [decidable_eq M]
  [add_group G] [add_action G X] [algorithmic_homogenous_space G X]

noncomputable def hhs_signature (x₀ : X) (n : ℕ) :
  signature M X G (vector (G × bool) n) :=
{ oracles := uniform_selecting ++ ((vector X n × M) →ₒ vector bool n),
  oracles_finite_range := by apply_instance,
  gen := λ _, do {
    sk ←$ᵗ G,
    return (sk +ᵥ x₀, sk)
  },
  sign := λ ⟨pk, sk, m⟩, do {
    (cs : vector G n) ← repeat_n ($ᵗ G) n,
    (ys : vector X n) ← return (cs.map (λ c, c +ᵥ pk)),
    (h : vector bool n) ← query (sum.inr ()) (ys, m),
    return (vector.zip_with (λ c (b : bool), (if b then c else c + sk, b)) cs h)
  },
  verify := λ ⟨pk, m, σ⟩, do {
    (ys : vector X n) ← return (σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀)),
    (h : vector bool n) ← query (sum.inr ()) (ys, m),
    return (h = σ.map prod.snd) 
  },
  gen_poly_time := sorry,
  sign_poly_time := sorry,
  verify_poly_time := sorry }

namespace signature_of_principal_action_class 
 
variable [h'' : algorithmic_homogenous_space G X]
include h''
variables (x₀ : X) (n : ℕ)

/-- We can coerce any uniform selection computation up to one for the oracles of `hhs_signature` -/
instance coe_uniform_selecting_oracles (A : Type) :
  has_coe (oracle_comp uniform_selecting A) (oracle_comp (hhs_signature G X M x₀ n).oracles A) :=
⟨λ oa, @has_coe.coe _ _ (coe_append_right uniform_selecting _ A) oa⟩
 
@[simp]
lemma support_coe_uniform_selecting_oracles {A : Type} (oa : oracle_comp uniform_selecting A) :
  support (oa : oracle_comp (hhs_signature G X M x₀ n).oracles A) = oa.support :=
sorry

@[simp]
lemma gen_apply (u : unit) :
  ((hhs_signature G X M x₀ n).gen u) = ↑($ᵗ G) >>= λ sk, return (sk +ᵥ x₀, sk) :=
rfl

lemma support_gen :
  ((hhs_signature G X M x₀ n).gen ()).support =
    set.range (λ (sk : G), (sk +ᵥ x₀, sk)) :=
by simp only [gen_apply, support_bind, support_coe_uniform_selecting_oracles,
  support_uniform_select_fintype, support_pure, set.Union_true, set.Union_singleton_eq_range]

theorem signature_of_principal_action_class_complete :
  (hhs_signature G X M x₀ n).complete :=
begin
  rw signature.complete_iff_signatures_support_subset,
  intros m pk sk σ hgen hsign,
  sorry
end

-- The choose_fork that will be passed to forking lemma
-- `q` will be the max queries of the adversary
def choose_fork {q : ℕ} (x₀ : X) (n : ℕ) (pk : X) (m : M) 
  (σ : vector (G × bool) n) (log : query_log $ ((vector X n × M) →ₒ vector bool n)) : 
  option (fin q) :=
let index' : option ℕ := log.index_of_input ()
  (σ.map (λ ⟨c, b⟩, if b then c +ᵥ pk else c +ᵥ x₀), m) in
match index' with
| none := none
| (some index) := if h : index < q then some ⟨index, h⟩ else none
end

end signature_of_principal_action_class