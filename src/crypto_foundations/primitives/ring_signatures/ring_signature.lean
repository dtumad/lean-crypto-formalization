import crypto_foundations.dist_sem
import crypto_foundations.vector_call
import computational_complexity.complexity_class
import computational_complexity.negligable
import data.list.basic

/-!
# Ring Signatures

This file defines ring signatures and ring signature schemes, and their cryptographic properties.
The security properties `complete`, `anonomyous`, and `unforgeable` are defined in terms of corresponding experiments.
-/

-- TODO: Old definition built in two steps, maybe better to eventually unbundle like this again
-- structure ring_signature (M : Type) (S : ℕ → Type) (PK SK : Type)
--   [decidable_eq PK] [decidable_eq SK] :=
-- (gen : comp (PK × SK))
-- (gen_well_formed : gen.is_well_formed)
-- (sign (n : ℕ) (i : fin n) (sk : SK) : vector PK n × M → comp (S n))
-- (sign_well_formed (n : ℕ) (i : fin n) (sk : SK) : ∀ inp, (sign n i sk inp).is_well_formed)
-- (verify (n : ℕ) : vector PK n × M × S n → bool)

-- structure ring_signature_scheme (M : Type) (S : ℕ → ℕ → Type) (PK SK : ℕ → Type)
--   [∀ sp, decidable_eq $ PK sp] [∀ sp, decidable_eq $ SK sp] :=
-- (rs (sp : ℕ) : ring_signature' M (S sp) (PK sp) (SK sp))
-- (gen_poly_time : poly_time_comp (λ sp, (rs sp).gen))
-- (sign_poly_time : false)
-- (verify_poly_time : ∀ n, poly_time_cost (λ sp, (rs sp).verify n))

/-- Definition of a ring signature, all methods take a security parameter `sp` as input.
`gen` returns a public key and secret key
`sign` returns a signature on a message, where `i : fin n` is the signer's index in the `n`-person ring
  and the list of signers is given in the form of an `n` element vector,
`verify` checks whether a given signature is valid on a ring and a message
-- TODO: Double check the polynomial time stuff, maybe more parameters should be included? -/
structure ring_signature (M : Type) (S : ℕ → ℕ → Type) (PK SK : ℕ → Type)
  [∀ sp, decidable_eq $ PK sp] [∀ sp, decidable_eq $ SK sp]
  [∀ sp n, decidable_eq $ S sp n] :=
(gen (sp : ℕ) : comp (PK sp × SK sp))
(gen_well_formed : ∀ sp, (gen sp).is_well_formed)
(gen_poly_time : complexity_class.poly_time_comp₀ gen)
(sign (sp n : ℕ) (i : fin n) (sk : SK sp) : (vector (PK sp) n) × M → comp (S sp n))
(sign_well_formed : ∀ sp n i sk inp, (sign sp n i sk inp).is_well_formed)
(sign_poly_time : ∀ (n : ℕ) (i : fin n) (sk : Π sp, SK sp), 
  complexity_class.poly_time_comp₁ (λ sp, sign sp n i (sk sp)))
(verify (sp n : ℕ) : vector (PK sp) n × M × S sp n → bool)
(verify_poly_time : ∀ (n : ℕ), complexity_class.poly_time_fun₁ (λ sp, verify sp n))

namespace ring_signature

variables {M : Type} {PK SK : ℕ → Type} {S : ℕ → ℕ → Type} 
variables [∀ sp, decidable_eq $ PK sp] [∀ sp, decidable_eq $ SK sp] 
variables [decidable_eq M] [∀ sp n, decidable_eq $ S sp n]
variables (rs : ring_signature M S PK SK) {sp : ℕ}

instance gen_well_formed' : (rs.gen sp).is_well_formed :=
rs.gen_well_formed sp

instance sign_well_formed' (n : ℕ) (i : fin n) (sk : SK sp) (inp : vector (PK sp) n × M):
  (rs.sign sp n i sk inp).is_well_formed :=
rs.sign_well_formed sp n i sk inp 

section complete

def completeness_experiment (rs : ring_signature M S PK SK) (sp n : ℕ) (i : fin n) (m : M) 
  : comp bool :=
comp.bind (comp.vector_call (rs.gen sp) n) (λ ks,
comp.bind (comp.ret $ vector.map prod.fst ks) (λ pks, 
comp.bind (rs.sign sp n i (vector.nth ks i).snd (pks, m)) (λ s,
comp.ret $ rs.verify sp n (pks, m, s))))

instance completeness_expiriement.is_well_formed (rs : ring_signature M S PK SK)
  (sp n : ℕ) (i : fin n) (m : M) : 
  (completeness_experiment rs sp n i m).is_well_formed :=
begin
  unfold completeness_experiment,
  apply_instance,
end

/-- A ring signature is complete if for any list if completeness experiment always succeeds `-/
def complete (rs : ring_signature M S PK SK) :=
∀ (sp n : ℕ) (i : fin n) (m : M), comp.Pr (completeness_experiment rs sp n i m) = 1

end complete

/-- Oracle on inputs `(s, m, ⟨l, i, R⟩)` returns `rs.sign sp i skₛ ⟨R, m⟩` -/
def signing_oracle_comp (rs : ring_signature M S PK SK) (sp n : ℕ) (A : Type) :=
oracle_comp (fin n × M × Σ (l : ℕ), fin l × vector (PK sp) l)
  (Σ (l : ℕ), with_bot $ S sp l) A

def temp_run {A : Type} [decidable_eq A] {rs : ring_signature M S PK SK} {sp n : ℕ}
  (t : signing_oracle_comp rs sp n A) (ks : vector (PK sp × SK sp) n) : comp A :=
begin
  refine (t.eval_distribution unit _ ()).bind (λ b, comp.ret b.1),
  rintros _ ⟨s, m, ⟨l, i, R⟩⟩,
  let pk : PK sp := (ks.nth s).1,
  let sk : SK sp := (ks.nth s).2,
  refine (rs.sign sp l i sk (R, m)).bind (λ σ, _),
  refine comp.ret (⟨l, _⟩, ()),
  refine if (R.nth i) = pk then σ else ⊥,
end

instance temp_run.is_well_formed {A : Type} [decidable_eq A] {rs : ring_signature M S PK SK} {sp n : ℕ}
  {t : signing_oracle_comp rs sp n A} {ks : vector (PK sp × SK sp) n} :
  (temp_run t ks).is_well_formed :=
begin
  simp [temp_run],
end

section anonomyous

-- `n` is the number of keys, will be polynomial in `sp`
-- Remember that the adversary can just ask for a challenge of something they've already seen previous oracle outputs for
-- TODO: better to have two adversaries?
-- Note that the second adversary gets all the secret keys as well
def anonomyous_experiment (rs : ring_signature M S PK SK) (sp n : ℕ)
  (A : vector (PK sp) n → signing_oracle_comp rs sp n (Σ (l : ℕ), M × (fin n × fin l) × (fin n × fin l) × (vector (PK sp) l)))
  (A' : vector (PK sp × SK sp) n → (Σ (l : ℕ), S sp l) → signing_oracle_comp rs sp n bool) : 
  comp bool :=
(comp.vector_call (rs.gen sp) n).bind (λ ks, begin
  let pks := vector.map prod.fst ks,
  let sks := vector.map prod.snd ks,
  refine comp.bind (temp_run (A pks) ks) (λ A_out, _),
  let l := A_out.1,
  let m : M := A_out.2.1,
  let i₀ : fin n × fin l := A_out.2.2.1,
  let i₁ : fin n × fin l := A_out.2.2.2.1,
  let R : vector (PK sp) l := A_out.2.2.2.2,
  refine comp.bind (comp.rnd bool) (λ b, _),
  let i : fin n × fin l := if b then i₁ else i₀,
  let sk : SK sp := (ks.nth i.1).2,
  refine (rs.sign sp l i.2 sk (R, m)).bind (λ σ, _),
  refine (temp_run (A' ks ⟨l, σ⟩) ks).bind (λ b', _),
  exact comp.ret (b' = b),
end)

-- TODO: need to show oracle_comp evaluation gives well_formed comp
instance anonomyous_experiment.is_well_formed (rs : ring_signature M S PK SK) (sp n : ℕ)
  (A : vector (PK sp) n → signing_oracle_comp rs sp n (Σ (l : ℕ), M × (fin n × fin l) × (fin n × fin l) × (vector (PK sp) l)))
  (A' : vector (PK sp × SK sp) n → (Σ (l : ℕ), S sp l) → signing_oracle_comp rs sp n bool) :
  (anonomyous_experiment rs sp n A A').is_well_formed :=
begin
  unfold anonomyous_experiment,
  simp,
  sorry,
  -- apply_instance,
end

-- TODO: Require `A` and `A'` have some poly_time hypothesis
def anonomyous (rs : ring_signature M S PK SK) :=
∀ (p : polynomial ℕ) (n : ℕ) (hn : n = p.eval sp)
  (A : Π sp, vector (PK sp) n → signing_oracle_comp rs sp n (Σ (l : ℕ), M × (fin n × fin l) × (fin n × fin l) × (vector (PK sp) l)))
  (A' : Π sp, vector (PK sp × SK sp) n → (Σ (l : ℕ), S sp l) → signing_oracle_comp rs sp n bool),
negligable (λ sp, begin
  haveI : (anonomyous_experiment rs sp n (A sp) (A' sp)).is_well_formed := 
    anonomyous_experiment.is_well_formed rs sp n (A sp) (A' sp),
  exact comp.Pr (anonomyous_experiment rs sp n (A sp) (A' sp)) - 0.5,
end)

end anonomyous

section unforgeable

-- TODO: A also needs a corruption oracle for this experiment
def unforgeable_experiment (rs : ring_signature M S PK SK) (sp n : ℕ)
  (A : vector (PK sp) n → signing_oracle_comp rs sp n (M × Σ (l : ℕ), vector (PK sp) l × S sp l)) : 
  comp bool :=
(comp.vector_call (rs.gen sp) n).bind (λ ks, begin
  let pks := vector.map prod.fst ks,
  let sks := vector.map prod.snd ks,
  refine comp.bind (temp_run (A pks) ks) (λ A_out, _),
  let m : M := A_out.1,
  let l : ℕ := A_out.2.1,
  let R : vector (PK sp) l := A_out.2.2.1,
  -- TODO: `R` should be a subset of `pks` - corrupted parties
  -- TODO: Adversary can't previously have queried Osign(*, m, R)
  let σ : S sp l := A_out.2.2.2,
  exact comp.ret (rs.verify sp l (R, m, σ)),
end)

def unforgeable (rs : ring_signature M S PK SK) :=
∀ (p : polynomial ℕ) (n : ℕ) (hn : n = p.eval sp)
  (A : Π sp, vector (PK sp) n → signing_oracle_comp rs sp n (M × Σ (l : ℕ), vector (PK sp) l × S sp l)),
negligable (λ sp, begin
  haveI : (unforgeable_experiment rs sp n (A sp)).is_well_formed := sorry,
  exact comp.Pr (unforgeable_experiment rs sp n (A sp)),
end)

end unforgeable

end ring_signature