import computational_complexity.complexity_class
import crypto_foundations.dist_sem
import computational_complexity.negligable

-- Extension of key type of the hash key to include the security_parameter
def hash_key (K : Type) := ℕ × K

-- Extract the security parameter from the hash key
def hash_key.sp {K : Type} : hash_key K → ℕ := λ k, k.1

-- Extract the actual key from the hash key
def hash_key.key {K : Type} : hash_key K → K := λ k, k.2

/-- `keygen` takes in a security parameter and outputs a key bundled with the parameter
  `hash` takes a `hash_key` from keygen and a string in the input space to a string in the output space -/
structure hash_function (K : Type) (input_space output_space : ℕ → Type) :=
(keygen (security_parameter : ℕ) : comp (hash_key K))
(keygen_well_formed : ∀ n, (keygen n).is_well_formed)
(keygen_correct : ∀ sp, (keygen sp).Pr_prop (λ k, k.sp = sp) = 1)
(hash (s : hash_key K) (x : input_space s.sp) : output_space s.sp)

variables {K : Type} {input_space output_space : ℕ → Type} [∀ n, decidable_eq (output_space n)]

@[simp]
instance hash_function.keygen.is_well_formed (H : hash_function K input_space output_space) (sp : ℕ) :
  (H.keygen sp).is_well_formed :=
hash_function.keygen_well_formed H sp

variable (H : hash_function K input_space output_space)

-- Because of correctness assumption, all elements in the support of keygen have matching security parameters
lemma security_parameter_eq_of_mem_support_keygen (H : hash_function K input_space output_space)
  (s : hash_key K) (n : ℕ) (hsn : s ∈ (H.keygen n).support) : s.sp = n :=
begin
  have := H.keygen_correct n,
  rw comp.Pr_prop_eq_one_iff at this,
  refine this s hsn,
end

/-- The security game for collision resistance as a probabalistic function. 
  Adversary implicitly recieves the secuirty parameter via the hashkey from `keygen`-/
def collision_finding_experiment (H : hash_function K input_space output_space) 
  (A : Π (s : hash_key K), comp ((input_space s.sp) × (input_space s.sp))) :
  ℕ → comp bool :=
λ security_parameter,
  comp.bind (H.keygen security_parameter) (λ s,
  comp.bind (A s) (λ xs, comp.ret (H.hash s xs.1 = H.hash s xs.2)
))

instance collision_finding_experiment.is_well_formed (H : hash_function K input_space output_space) 
  (A : Π (s : hash_key K), comp ((input_space s.sp) × (input_space s.sp)))
  (hA : ∀ (s : hash_key K), s ∈ (H.keygen s.sp).support → (A s).is_well_formed) 
  (n : ℕ) : (collision_finding_experiment H A n).is_well_formed :=
begin
  simp [collision_finding_experiment],
  refine λ s hs, hA s _,
  exact (security_parameter_eq_of_mem_support_keygen H s n hs).symm ▸ hs
end

def negligable_expirement_success (exp : ℕ → comp bool) (h : ∀ n, (exp n).is_well_formed) : Prop :=
negligable (λ n, comp.Pr (exp n))

-- TODO: look at poly-time requirements more closely
def collision_resistant (H : hash_function K input_space output_space) : Prop :=
∀ (A : Π (s : hash_key K), comp ((input_space s.sp) × (input_space s.sp)))
  (hA : ∀ (b : hash_key K), b ∈ (H.keygen b.sp).support → (A b).is_well_formed)
  (hA' : ∀ k, poly_time_comp (λ n, A (n, k))),
negligable_expirement_success (collision_finding_experiment H A) 
  (collision_finding_experiment.is_well_formed H A hA)