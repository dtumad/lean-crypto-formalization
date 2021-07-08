import computational_complexity.complexity_class
import crypto_foundations.dist_sem
import computational_complexity.negligable

/-!
# Hash Functions

This file defines the notion of a keyed hash function.

TODO: Think about using `encodable` type-class
-/
structure hash_function (K I O : Type) :=
(keygen : comp K)
(keygen_is_well_formed : keygen.is_well_formed)
(hash (key : K) (m : I) : O)

namespace hash_function

variables {K I O : Type} (h : hash_function K I O)

instance keygen.is_well_formed (h : hash_function K I O) :
  h.keygen.is_well_formed :=
h.keygen_is_well_formed

variables [decidable_eq O]

/-- The security game for collision resistance as a probabalistic function. -/
@[derive comp.is_well_formed]
def collision_finding_experiment (h : hash_function K I O) 
  (A : K → comp (I × I)) [∀ k, (A k).is_well_formed] : comp bool :=
comp.bind (h.keygen) (λ k,
comp.bind (A k) (λ xs, 
comp.ret (h.hash k xs.1 = h.hash k xs.2)))

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

structure collision_finding_adversary (H : hash_scheme K I O) :=
(adv : Π (sp : ℕ), K sp → comp ((I sp) × (I sp)))
(wf : ∀ sp k, (adv sp k).is_well_formed)
(pt : complexity_class.poly_time_comp₁ adv)

instance collision_finding_adversary.is_well_formed
  {H : hash_scheme K I O} (A : collision_finding_adversary H)
  (sp : ℕ) (k : K sp) : (A.adv sp k).is_well_formed :=
A.wf sp k

def collision_resistant (H : hash_scheme K I O) : Prop :=
∀ (A : collision_finding_adversary H),
asymptotics.negligable (λ sp, 
  comp.Pr ((H.scheme sp).collision_finding_experiment (A.adv sp)))

end hash_scheme