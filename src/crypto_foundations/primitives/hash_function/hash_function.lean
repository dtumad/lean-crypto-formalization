import computational_complexity.complexity_class
import crypto_foundations.dist_sem
import computational_complexity.negligable

/-!
# Hash Functions

This file defines the notion of a keyed hash function.

-/

/-- `keygen` takes in a security parameter and outputs a key bundled with the parameter
  `hash` takes a `hash_key` from keygen and a string in the input space to a string in the output space -/
structure hash_function (K : ℕ → Type) (input_space output_space : ℕ → Type) :=
(keygen (sp : ℕ) : comp (K sp))
(keygen_well_formed : ∀ sp, (keygen sp).is_well_formed)
(keygen_poly_time : poly_time_comp keygen)
(hash {sp : ℕ} : K sp × input_space sp → output_space sp)
(hash_poly_time : poly_time_cost @hash)

variables {K : ℕ → Type} {input_space output_space : ℕ → Type} [∀ n, decidable_eq (output_space n)]

@[simp]
instance hash_function.keygen.is_well_formed (H : hash_function K input_space output_space) (sp : ℕ) :
  (H.keygen sp).is_well_formed :=
hash_function.keygen_well_formed H sp

variable (H : hash_function K input_space output_space)

/-- The security game for collision resistance as a probabalistic function. 
  Adversary implicitly recieves the secuirty parameter via the hashkey from `keygen`-/
def collision_finding_experiment (H : hash_function K input_space output_space) 
  (A : Π (sp : ℕ) (k : K sp), comp ((input_space sp) × (input_space sp))) :
  ℕ → comp bool :=
λ sp,
  comp.bind (H.keygen sp) (λ k,
  comp.bind (A sp k) (λ xs, comp.ret (H.hash (k, xs.1) = H.hash (k, xs.2))
))

@[simp]
lemma collision_finding_experiment.is_well_formed (H : hash_function K input_space output_space)
  (A : Π (sp : ℕ) (k : K sp), comp ((input_space sp) × (input_space sp))) 
  (sp : ℕ) : (collision_finding_experiment H A sp).is_well_formed ↔ 
    (∀ (k : K sp), k ∈ (H.keygen sp).support → (A sp k).is_well_formed)  :=
by simp [collision_finding_experiment]

def negligable_expirement_success (exp : ℕ → comp bool) (h : ∀ sp, (exp sp).is_well_formed) : Prop :=
negligable (λ sp, comp.Pr (exp sp))

def collision_resistant (H : hash_function K input_space output_space) : Prop :=
∀ (A : Π (sp : ℕ) (k : K sp), comp ((input_space sp) × (input_space sp)))
  (A_efficient : ∀ (k : Π sp, K sp), poly_time_comp (λ sp, A sp (k sp)))
  (A_well_formed : ∀ (sp : ℕ) (k : K sp) , k ∈ (H.keygen sp).support → (A sp k).is_well_formed),
negligable_expirement_success (collision_finding_experiment H A) (by simpa using hA)