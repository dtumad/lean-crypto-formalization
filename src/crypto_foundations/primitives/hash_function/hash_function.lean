import computational_complexity.complexity_class
import crypto_foundations.dist_sem
import computational_complexity.negligable

/-!
# Hash Functions

This file defines the notion of a keyed hash function.

TODO: Think about using `encodable` type-class
-/

def negligable_expirement_success (exp : ℕ → comp bool) (h : ∀ sp, (exp sp).is_well_formed) : Prop :=
asymptotics.negligable (λ sp, comp.Pr (exp sp))

structure hash_function (K I O : Type) :=
(keygen : comp K)
(keygen_is_well_formed : keygen.is_well_formed)
(hash (key : K) (m : I) : O)

namespace hash_function

variables {K I O : Type} (h : hash_function K I O)

@[simp]
instance keygen.is_well_formed (h : hash_function K I O) :
  h.keygen.is_well_formed :=
h.keygen_is_well_formed

variables [decidable_eq O]

/-- The security game for collision resistance as a probabalistic function. -/
def collision_finding_experiment (h : hash_function K I O) 
  (A : K → comp (I × I)) : comp bool :=
comp.bind (h.keygen) (λ k,
comp.bind (A k) (λ xs, 
comp.ret (h.hash k xs.1 = h.hash k xs.2)))

@[simp]
lemma collision_finding_experiment_is_well_formed_iff (h : hash_function K I O)
  (a : K → comp (I × I)) : 
  (h.collision_finding_experiment a).is_well_formed ↔ 
    (∀ (k : K), k ∈ (h.keygen).support → (a k).is_well_formed)  :=
by simp [collision_finding_experiment]

instance collision_finding_experiment.is_well_formed (h : hash_function K I O) 
  (a : K → comp (I × I)) (ha : ∀ k, (a k).is_well_formed) :
  (h.collision_finding_experiment a).is_well_formed :=
begin
  rw [collision_finding_experiment_is_well_formed_iff],
  exact λ k _, ha k,
end

end hash_function

/-- `keygen` takes in a security parameter and outputs a key bundled with the parameter
  `hash` takes a `hash_key` from keygen and a string in the input space to a string in the output space -/
structure hash_scheme (K I O : ℕ → Type) :=
(scheme (sp : ℕ) : hash_function (K sp) (I sp) (O sp))
(keygen_poly_time : complexity_class.poly_time_comp₀ (λ sp, (scheme sp).keygen))
(hash_poly_time : complexity_class.poly_time_fun₂ (λ sp, (scheme sp).hash))

namespace hash_scheme

variables {K I O : ℕ → Type} {H : hash_scheme K I O}

section projections

variable (H)

def keygen (sp : ℕ) : comp (K sp) :=
(H.scheme sp).keygen

@[simp]
lemma keygen_eq (sp : ℕ) :
  H.keygen sp = (H.scheme sp).keygen := rfl

def hash {sp : ℕ} (k : K sp) (i : I sp) : O sp :=
(H.scheme sp).hash k i

@[simp]
lemma hash_eq {sp : ℕ} (k : K sp) (i : I sp) :
  H.hash k i = (H.scheme sp).hash  k i:= rfl

end projections

variables [∀ n, decidable_eq $ O n]

def collision_finding_adversary (H : hash_scheme K I O) :=
Π (sp : ℕ), K sp → comp ((I sp) × (I sp))

class collision_finding_adversary.admissable {H : hash_scheme K I O}
  (A : collision_finding_adversary H) :=
(is_well_formed : ∀ sp k, (A sp k).is_well_formed)
(poly_time : complexity_class.poly_time_comp₁ A)

instance collision_finding_adversary.is_well_formed
  {H : hash_scheme K I O} {A : collision_finding_adversary H}
  (hA : A.admissable) (sp : ℕ) (k : K sp) :
  (A sp k).is_well_formed :=
collision_finding_adversary.admissable.is_well_formed H sp k

/-- The security game for collision resistance as a probabalistic function. 
  Adversary implicitly recieves the secuirty parameter via the hashkey from `keygen`-/
def collision_finding_experiment (H : hash_scheme K I O) 
  (A : collision_finding_adversary H) (sp : ℕ) : comp bool :=
(H.scheme sp).collision_finding_experiment (A sp)

@[simp]
lemma collision_finding_experiment_is_well_formed_iff (H : hash_scheme K I O) 
  (A : collision_finding_adversary H) (sp : ℕ) :
  (H.collision_finding_experiment A sp).is_well_formed ↔
    ∀ k ∈ (H.keygen sp).support, (A sp k).is_well_formed :=
by simp [hash_scheme.collision_finding_experiment]

instance collision_finding_experiment.is_well_formed (H : hash_scheme K I O)
  (A : collision_finding_adversary H) (hA : A.admissable) (sp : ℕ) :
  (H.collision_finding_experiment A sp).is_well_formed :=
begin
  refine hash_function.collision_finding_experiment.is_well_formed _ _ _,
  refine collision_finding_adversary.is_well_formed hA sp,
end

def collision_resistant (H : hash_scheme K I O) : Prop :=
∀ (A : collision_finding_adversary H) (hA : A.admissable),
negligable_expirement_success (H.collision_finding_experiment A)
  (collision_finding_experiment.is_well_formed H A hA)

end hash_scheme