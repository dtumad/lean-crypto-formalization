import crypto_foundations.computational_monads.dist_sem
import crypto_foundations.computational_monads.vector_call
import computational_complexity.complexity_class
import computational_complexity.negligable
import data.list.basic

/-!
# Ring Signatures

This file defines ring signatures and ring signature schemes, and their cryptographic properties.
The security properties `complete`, `anonomyous`, and `unforgeable` are defined in terms of corresponding experiments.

TODO: Closely double check the non-completeness security definitions before getting to far proving them
-/

section signing_ring

structure signing_ring (n : ℕ) (PK : Type) :=
(mems : vector PK n)
(i : fin n)

def signing_ring.pk {PK : Type} {n : ℕ}
  (R : signing_ring n PK) : PK :=
R.mems.nth R.i

structure signing_input (n : ℕ) (PK SK M : Type) :=
(R : signing_ring n PK)
(sk : SK)
(m : M)

structure verification_input (n : ℕ) (PK M : Type) (S : ℕ → Type) :=
(mems : vector PK n)
(m : M)
(σ : S n)

end signing_ring

/-- Definition of a ring signature, all methods take a security parameter `sp` as input.
`gen` returns a public key and secret key
`sign` returns a signature on a message, where `i : fin n` is the signer's index in the `n`-person ring
  and the list of signers is given in the form of an `n` element vector,
`verify` checks whether a given signature is valid on a ring and a message -/
structure ring_signature (M : Type) (S : ℕ → Type) (PK SK : Type)
  [decidable_eq M] [decidable_eq PK] :=
(gen : unit → comp (PK × SK))
(gen_well_formed : (gen ()).is_well_formed)
(sign (n : ℕ) : signing_input n PK SK M → comp (S n))
(sign_well_formed : ∀ n inp, (sign n inp).is_well_formed)
(verify (n : ℕ) : verification_input n PK M S → bool)

namespace ring_signature

variables {M : Type} {S : ℕ → Type} {PK SK : Type}
variables [decidable_eq M] [decidable_eq PK]
variables (rs : ring_signature M S PK SK)

@[simp]
instance gen.is_well_formed : (rs.gen ()).is_well_formed :=
rs.gen_well_formed

@[simp]
instance sign.is_well_formed (n : ℕ) (inp : signing_input n PK SK M) :
  (rs.sign n inp).is_well_formed :=
rs.sign_well_formed _ inp

section complete

@[derive comp.is_well_formed]
def completeness_experiment (n : ℕ) (i : fin n) (m : M) : comp bool :=
do ks ← (comp.vector_call (rs.gen ()) n),
  mems ← return (vector.map prod.fst ks), 
  σ ← (rs.sign n ⟨⟨mems, i⟩, (vector.nth ks i).2, m⟩),
  return (rs.verify n ⟨mems, m, σ⟩)

@[simp]
lemma mem_support_completeness_experiment_iff (n : ℕ) (i : fin n) (m : M) (b : bool) :
  b ∈ (completeness_experiment rs n i m).support ↔
    ∃ (ks : vector (PK × SK) n) (hks : ∀ (i : fin n), ks.nth i ∈ (rs.gen ()).support)
      (σ : S n) (hσ : σ ∈ (rs.sign n ⟨⟨vector.map prod.fst ks, i⟩, (vector.nth ks i).2, m⟩).support),
      b = rs.verify n ⟨vector.map prod.fst ks, m, σ⟩ :=
by simp [completeness_experiment]

/-- A ring signature is complete if for any list if completeness experiment always succeeds `-/
def complete :=
∀ (n : ℕ) (i : fin n) (m : M), comp.Pr (completeness_experiment rs n i m) = 1

end complete

section ring_sig_oracle

/-- Definition of a probabalistic computaiton with oracle signing access
  `n` is the global number of `PK × SK` pairs used in the simulation. -/
def signing_oracle_comp (rs : ring_signature M S PK SK) (n : ℕ) (T : Type) :=
oracle_comp (λ (l : ℕ), signing_ring l PK × M)
  (λ (l : ℕ), with_bot $ S l) T

variables {rs}

/--
  returns `⊥` if the `pk` specified by the signing ring isn't in `ks` -/
def signing_oracle_comp.logging_eval_distribution {n : ℕ} {T : Type}
  (t : signing_oracle_comp rs n T) (ks : vector (PK × SK) n) : 
    comp (T × list (Σ (l : ℕ), signing_ring l PK × M)) :=
t.logging_eval_distribution (λ l inp,
  let k : with_bot (PK × SK) := list.find (λ k, k.1 = inp.1.pk) ks.to_list in
  begin 
    refine k.elim (return ⊥) (λ k, _),
    refine (rs.sign _ ⟨inp.1, k.2, inp.2⟩).bind (λ σ, return $ some σ),
  end
)

@[simp]
instance signing_oracle_comp.logging_eval_distribution.is_well_formed 
  {n : ℕ} {T : Type} (t : signing_oracle_comp rs n T) 
  [ht : t.is_well_formed] (ks : vector (PK × SK) n) :
  (t.logging_eval_distribution ks).is_well_formed :=
by simp [signing_oracle_comp.logging_eval_distribution]

@[derive comp.is_well_formed]
def signing_oracle_comp.eval_distribution {n : ℕ} {T : Type}
  (t : signing_oracle_comp rs n T) [ht : t.is_well_formed] (ks : vector (PK × SK) n) :
  comp T :=
do t ← (t.logging_eval_distribution ks),
  return t.1

end ring_sig_oracle

section unforgeable_experiment

-- TODO: A also needs a corruption oracle for this experiment
@[derive comp.is_well_formed]
def unforgeable_experiment (n : ℕ)
  (A : vector PK n → signing_oracle_comp rs n (Σ (n : ℕ), verification_input n PK M S)) 
  [hA : ∀ pks, (A pks).is_well_formed] : comp bool :=
do ks ← comp.vector_call (rs.gen ()) n, 
  pks ← return (vector.map prod.fst ks),
  sks ← return (vector.map prod.snd ks),
  A_out ← (A pks).logging_eval_distribution ks,
  m ← return A_out.1.2.m,
  uncorrupted_parties ← return (A_out.1.2.mems.to_list.filter (λ pk, false)), -- TODO
  -- Check that the forged signature is on an ucorrupted ring
  R_okay ← return (A_out.1.2.mems.to_list ⊆ uncorrupted_parties : bool),
  log ← return A_out.2,
  -- Check if they previously got a `R`-signature for message `m`
  log_okay ← return (¬ log.any (λ x, m = x.2.2 ∧ (list.perm A_out.1.2.mems.to_list x.2.1.mems.to_list)) : bool),
  σ ← return A_out.1.2.σ,
  return (if R_okay ∧ log_okay then (rs.verify _ ⟨A_out.1.2.1, m, σ⟩) else false)

end unforgeable_experiment

section anonomyous_experiment

/-- `n` is the number of keys generated, will be polynomial in `sp`
-- Remember that the adversary can just ask for a challenge of something they've already seen previous oracle outputs for
-- Note that the second adversary gets all the secret keys as well -/
@[derive comp.is_well_formed]
def anonomyous_experiment {A_state : Type} (n : ℕ)
  (A : vector PK n → signing_oracle_comp rs n (Σ (l : ℕ), M × (fin n × fin l) × (fin n × fin l) × (vector PK l) × A_state))
  (A' : A_state → vector (PK × SK) n → (Σ (l : ℕ), S l) → signing_oracle_comp rs n bool)
  [hA : ∀ pks, (A pks).is_well_formed] [hA' : ∀ st ks σ, (A' st ks σ).is_well_formed] : 
  comp bool :=
do ks ← (comp.vector_call (rs.gen ()) n),
  A_out ← ((A (vector.map prod.fst ks)).eval_distribution ks),
  m ← return A_out.2.1,
  i₀ ← return A_out.2.2.1,
  i₁ ← return A_out.2.2.2.1,
  R ← return A_out.2.2.2.2.1,
  state ← return A_out.2.2.2.2.2,
  b ← comp.rnd bool,
  i ← return (if b then i₁ else i₀),
  sk ← return (ks.nth i.1).2,
  σ ← rs.sign _ ⟨⟨R, i.2⟩, sk, m⟩,
  b' ← (A' state ks ⟨A_out.1, σ⟩).eval_distribution ks,
  comp.ret (b' = b)

end anonomyous_experiment

end ring_signature

variables [function_cost_model ℚ] [comp_cost_model ℚ]

structure ring_signature_scheme (M : Type) (S : ℕ → ℕ → Type) (PK SK : ℕ → Type)
  [decidable_eq M] [∀ sp, decidable_eq $ PK sp] :=
(rs (sp : ℕ) : ring_signature M (S sp) (PK sp) (SK sp))
(gen_poly_time : complexity_class.polynomial_complexity (λ sp, (rs sp).gen))
(sign_poly_time (n : ℕ) : complexity_class.polynomial_complexity (λ sp, (rs sp).sign n))
(verify_poly_time (n : ℕ) : complexity_class.polynomial_complexity (λ sp, (rs sp).verify n))

namespace ring_signature_scheme

open ring_signature

variables {M : Type} {S : ℕ → ℕ → Type} {PK SK : ℕ → Type}
variables [decidable_eq M] [∀ sp, decidable_eq $ PK sp]
variable (rss : ring_signature_scheme M S PK SK)

section unforgeable

structure unforgeable_adversary (p : polynomial ℕ) := 
(adv (sp : ℕ) (pks : vector (PK sp) (p.eval sp)) :
  signing_oracle_comp (rss.rs sp) (p.eval sp) 
    (Σ (n : ℕ), verification_input n (PK sp) M (S sp)))
(wf : ∀ sp pks, (adv sp pks).is_well_formed)
(poly_time : true)

instance unforgeable_adversary.is_well_formed
  {p : polynomial ℕ} (A : unforgeable_adversary rss p) 
  (sp : ℕ) (pks : vector (PK sp) (p.eval sp)) :
  (A.adv sp pks).is_well_formed :=
A.wf sp pks

def unforgeable := 
∀ {p : polynomial ℕ} (A : unforgeable_adversary rss p),
  asymptotics.negligable (λ sp, 
    comp.Pr (unforgeable_experiment (rss.rs sp) (p.eval sp) (A.adv sp)))

end unforgeable

section anonomyous

structure anonomyous_adversary (p : polynomial ℕ) :=
(state : Type)
(adv₁ (sp : ℕ) (pks : vector (PK sp) (p.eval sp)) : 
  signing_oracle_comp (rss.rs sp) (p.eval sp)
      (Σ (l : ℕ), M × (fin (p.eval sp) × fin l) 
          × (fin (p.eval sp) × fin l) × (vector (PK sp) l) × state))
(adv₂ (sp : ℕ) (st : state) (ks : vector (PK sp × SK sp) (p.eval sp))
  (σ : Σ (l : ℕ), S sp l) : signing_oracle_comp (rss.rs sp) (p.eval sp) bool)
(adv₁_wf : ∀ sp pks, (adv₁ sp pks).is_well_formed)
(adv₂_wf : ∀ sp st ks σ, (adv₂ sp st ks σ).is_well_formed)
(adv₁_pt : true)
(adv₂_pt : true)

instance anonomyous_adversary.adv₁.is_well_formed 
  {p : polynomial ℕ} (A : anonomyous_adversary rss p)
  (sp : ℕ) (pks : vector (PK sp) (p.eval sp)) :
  (A.adv₁ sp pks).is_well_formed :=
A.adv₁_wf sp pks

instance anonomyous_adversary.adv₂.is_well_formed
  {p : polynomial ℕ} (A : anonomyous_adversary rss p)
  (sp : ℕ) (st : A.state) (ks : vector (PK sp × SK sp) (p.eval sp))
  (σ : Σ (l : ℕ), S sp l) : (A.adv₂ sp st ks σ).is_well_formed :=
A.adv₂_wf sp st ks σ

def anonomyous := 
∀ (p : polynomial ℕ) (A : anonomyous_adversary rss p),
asymptotics.negligable (λ sp, 
  comp.Pr (anonomyous_experiment (rss.rs sp) (p.eval sp) (A.adv₁ sp) (A.adv₂ sp)) - 0.5)

end anonomyous

end ring_signature_scheme