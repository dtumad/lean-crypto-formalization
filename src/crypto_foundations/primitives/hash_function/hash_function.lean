import computational_complexity.complexity_class
import crypto_foundations.dist_sem
import computational_complexity.negligable

/-!
# Hash Functions

This file defines the notion of a keyed hash function.

TODO: Think about using `encodable` type-class
-/

section hash_f

structure hash_f (K I O : Type) :=
(keygen : comp K)
(keygen_is_well_formed : keygen.is_well_formed)
(hash (key : K) (m : I) : O)

variables {K I O : Type} (h : hash_f K I O)

@[simp]
instance hash_f.keygen.is_well_formed (h : hash_f K I O) :
  h.keygen.is_well_formed :=
h.keygen_is_well_formed

variables [decidable_eq O]

/-- The security game for collision resistance as a probabalistic function. -/
def hash_f.collision_finding_experiment (h : hash_f K I O) 
  (a : K → comp (I × I)) : comp bool :=
comp.bind (h.keygen) (λ k,
comp.bind (a k) (λ xs, 
comp.ret (h.hash k xs.1 = h.hash k xs.2)))

@[simp]
lemma collision_finding_experiment_is_well_formed_iff (h : hash_f K I O)
  (a : K → comp (I × I)) : 
  (h.collision_finding_experiment a).is_well_formed ↔ 
    (∀ (k : K), k ∈ (h.keygen).support → (a k).is_well_formed)  :=
by simp [hash_f.collision_finding_experiment]

instance collision_finding_experiment.is_well_formed (h : hash_f K I O) 
  (a : K → comp (I × I)) [ha : ∀ k, (a k).is_well_formed] :
  (h.collision_finding_experiment a).is_well_formed :=
begin
  rw [collision_finding_experiment_is_well_formed_iff],
  exact λ k _, ha k,
end

end hash_f

section hash_scheme

/-- `keygen` takes in a security parameter and outputs a key bundled with the parameter
  `hash` takes a `hash_key` from keygen and a string in the input space to a string in the output space -/
structure hash_scheme (K I O : ℕ → Type) :=
(scheme (sp : ℕ) : hash_f (K sp) (I sp) (O sp))
(keygen_poly_time : complexity_class.poly_time_comp₀ (λ sp, (scheme sp).keygen))
(hash_poly_time : complexity_class.poly_time_fun₂ (λ sp, (scheme sp).hash))

variables {K I O : ℕ → Type} (H : hash_scheme K I O)

section projections

def hash_scheme.keygen (sp : ℕ) : comp (K sp) :=
(H.scheme sp).keygen

@[simp]
lemma hash_scheme.keygen_eq (sp : ℕ) :
  H.keygen sp = (H.scheme sp).keygen := rfl

def hash_scheme.hash {sp : ℕ} (k : K sp) (i : I sp) : O sp :=
(H.scheme sp).hash k i

@[simp]
lemma hash_scheme.hash_eq {sp : ℕ} (k : K sp) (i : I sp) :
  H.hash k i = (H.scheme sp).hash  k i:= rfl

end projections

variables [∀ n, decidable_eq $ O n]

/-- The security game for collision resistance as a probabalistic function. 
  Adversary implicitly recieves the secuirty parameter via the hashkey from `keygen`-/
def hash_scheme.collision_finding_experiment (H : hash_scheme K I O) 
  (A : Π (sp : ℕ), K sp → comp ((I sp) × (I sp))) (sp : ℕ) : comp bool :=
(H.scheme sp).collision_finding_experiment (A sp)

def negligable_expirement_success (exp : ℕ → comp bool) (h : ∀ sp, (exp sp).is_well_formed) : Prop :=
asymptotics.negligable (λ sp, comp.Pr (exp sp))

def collision_resistant (H : hash_scheme K I O) : Prop :=
∀ (A : Π (sp : ℕ), K sp → comp ((I sp) × (I sp)))
  (A_efficient : complexity_class.poly_time_comp₁ A)
  [A_well_formed : ∀ (sp : ℕ) (k : K sp) (hk : k ∈ (H.scheme sp).keygen.support), (A sp k).is_well_formed],
negligable_expirement_success (λ sp, (H.scheme sp).collision_finding_experiment (A sp)) (by simpa)

end hash_scheme