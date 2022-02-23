import computational_monads.probabalistic_computation.constructions
import computational_monads.oracle_access.oracle_comp

open_locale nnreal ennreal

noncomputable theory

namespace oracle_comp

variables {T U A X : Type} [decidable_eq T] [fintype U] [nonempty U]

def acc_e (input_generator : prob_comp X)
  (adv : X → oracle_comp ⟦T →ᵒ U⟧ A)
  (validate : A → prob_comp (option T)) :
  prob_comp (option T) :=
do {
  x ← input_generator,
  (σ, log) ← simulate (random_oracle T U) (adv x) [],
  validate σ
}

def accepting_experiment (adv : oracle_comp ⟦T →ᵒ U⟧ A)
  (validate : A × list (T × U) → prob_comp (option T)) : prob_comp (option T) :=
do {
  (σ, log) ← simulate (random_oracle T U) adv [],
  validate (σ, log)
}

def acc (adv : oracle_comp ⟦T →ᵒ U⟧ A)
  (validate : A → prob_comp (option T)) : ℝ≥0∞ :=
(accepting_experiment adv validate).prob_event
  (λ t, t.is_some)

constant fork (adv : oracle_comp ⟦T →ᵒ U⟧ A) :
  oracle_comp ⟦T →ᵒ U⟧ (A × A)

def forking_experiment (adv : oracle_comp ⟦T →ᵒ U⟧ A)
  (validate : A → prob_comp (option T)) : prob_comp (option T × option T) :=
do {
  ((σ, σ'), log) ← simulate (random_oracle T U) (fork adv) [],
  t1 ← validate σ,
  t2 ← validate σ',
  return (t1, t2)
}

def fork_success {T : Type*} : option T × option T → Prop
| ((some t), (some t')) := t ≠ t'
| _ := false

def frk (adv : oracle_comp ⟦T →ᵒ U⟧ A)
  (validate : A → prob_comp (option T)) : ℝ≥0∞ :=
(forking_experiment adv validate).prob_event
  fork_success

axiom forking_lemma (adv : oracle_comp ⟦T →ᵒ U⟧ A)
  (q : ℕ) (hq : queries_at_most adv q)
  (validate : A → prob_comp (option T)) :
  (frk)


end oracle_comp


-- end prob_comp 