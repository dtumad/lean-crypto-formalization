import crypto_foundations.dist_sem
import crypto_foundations.vector_call
import computational_complexity.complexity_class
import computational_complexity.negligable
import data.list.basic

/-!
# Ring Signatures

This file defines ring signatures and ring signature schemes, and their cryptographic properties.
The security properties `complete`, `anonomyous`, and `unforgeable` are defined in terms of corresponding experiments.

TODO: Closely double check the security definitions before getting to far proving them
-/

/-- Definition of a ring signature, all methods take a security parameter `sp` as input.
`gen` returns a public key and secret key
`sign` returns a signature on a message, where `i : fin n` is the signer's index in the `n`-person ring
  and the list of signers is given in the form of an `n` element vector,
`verify` checks whether a given signature is valid on a ring and a message
-- TODO: Double check the polynomial time stuff, maybe more parameters should be included in them? -/
structure ring_sig (M : Type) (S : ℕ → Type) (PK SK : Type)
  [decidable_eq PK] :=
(gen : comp (PK × SK))
(gen_well_formed : gen.is_well_formed)
(sign (n : ℕ) (i : fin n) (sk : SK) (R : vector PK n) (m : M) : comp (S n))
(sign_well_formed : ∀ n i sk R m, (sign n i sk R m).is_well_formed)
(verify (n : ℕ) (R : vector PK n) (m : M) (σ : S n) : bool)

namespace ring_sig

variables {M : Type} {S : ℕ → Type} {PK SK : Type}
variables [decidable_eq PK]
-- variables [decidable_eq M] [∀ n, decidable_eq $ S n]
variables (rs : ring_sig M S PK SK)

@[simp]
instance gen_well_formed' : (rs.gen).is_well_formed :=
rs.gen_well_formed

@[simp]
instance sign_well_formed' (n : ℕ) (i : fin n) (sk : SK) (R : vector PK n) (m : M) :
  (rs.sign n i sk R m).is_well_formed :=
rs.sign_well_formed n i sk R m 

section complete

def completeness_experiment (n : ℕ) (i : fin n) (m : M) : comp bool :=
comp.bind (comp.vector_call (rs.gen) n) (λ ks,
comp.bind (comp.ret $ vector.map prod.fst ks) (λ R, 
comp.bind (rs.sign n i (vector.nth ks i).snd R m) (λ σ,
comp.ret $ rs.verify n R m σ)))

@[simp]
instance completeness_expiriement.is_well_formed (n : ℕ) (i : fin n) (m : M) : 
  (completeness_experiment rs n i m).is_well_formed :=
by simp [completeness_experiment]

/-- A ring signature is complete if for any list if completeness experiment always succeeds `-/
def complete :=
∀ (n : ℕ) (i : fin n) (m : M), comp.Pr (completeness_experiment rs n i m) = 1

end complete

section ring_sig_oracle

/-- Definition of a probabalistic computaiton with oracle signing access
  `n` is the global number of `PK × SK` pairs used in the simulation -/
def signing_oracle_comp (rs : ring_sig M S PK SK) (n : ℕ) (T : Type) :=
oracle_comp (fin n × M × Σ (l : ℕ), fin l × vector PK l)
  (Σ (l : ℕ), with_bot $ S l) T

variables {rs}

def signing_oracle_comp.simulate
  {n : ℕ} {T : Type}
  (t : signing_oracle_comp rs n T) (ks : vector (PK × SK) n) : comp T :=
t.stateless_eval_distribution (λ inp,
  let s : fin n := inp.1 in
  let m : M := inp.2.1 in
  let l : ℕ := inp.2.2.1 in
  let i : fin l := inp.2.2.2.1 in
  let R : vector PK l := inp.2.2.2.2 in
  let pk := (ks.nth s).1 in
  let sk := (ks.nth s).2 in
  do σ ← (rs.sign l i sk R m),
    return ⟨l, if (R.nth i) = pk then σ else ⊥⟩
)

@[simp]
instance signing_oracle_comp.simulate.is_well_formed {n : ℕ} {T : Type}
  (t : signing_oracle_comp rs n T) [ht : t.is_well_formed] (ks : vector (PK × SK) n) :
  (t.simulate ks).is_well_formed :=
begin
  simp [signing_oracle_comp.simulate],
end

end ring_sig_oracle

section anonomyous_experiment

-- `n` is the number of keys, will be polynomial in `sp`
-- Remember that the adversary can just ask for a challenge of something they've already seen previous oracle outputs for
-- TODO: better to have two adversaries?
-- Note that the second adversary gets all the secret keys as well
def anonomyous_experiment (n : ℕ)
  (A : vector PK n → signing_oracle_comp rs n (Σ (l : ℕ), M × (fin n × fin l) × (fin n × fin l) × (vector PK l)))
  (A' : vector (PK × SK) n → (Σ (l : ℕ), S l) → signing_oracle_comp rs n bool) : 
  comp bool :=
(comp.vector_call (rs.gen) n).bind (λ ks, begin
  let pks := vector.map prod.fst ks,
  let sks := vector.map prod.snd ks,
  refine comp.bind ((A pks).simulate ks) (λ A_out, _),
  let l := A_out.1,
  let m : M := A_out.2.1,
  let i₀ : fin n × fin l := A_out.2.2.1,
  let i₁ : fin n × fin l := A_out.2.2.2.1,
  let R : vector PK l := A_out.2.2.2.2,
  refine comp.bind (comp.rnd bool) (λ b, _),
  let i : fin n × fin l := if b then i₁ else i₀,
  let sk : SK := (ks.nth i.1).2,
  refine (rs.sign l i.2 sk R m).bind (λ σ, _),
  refine ((A' ks ⟨l, σ⟩).simulate ks).bind (λ b', _),
  exact comp.ret (b' = b),
end)

@[simp]
instance anonomyous_experiment.is_well_formed (n : ℕ)
  (A : vector PK n → signing_oracle_comp rs n (Σ (l : ℕ), M × (fin n × fin l) × (fin n × fin l) × (vector PK l)))
  (A' : vector (PK × SK) n → (Σ (l : ℕ), S l) → signing_oracle_comp rs n bool)
  [hA : ∀ pks, (A pks).is_well_formed] [hA' : ∀ ks σ, (A' ks σ).is_well_formed] :
  (anonomyous_experiment rs n A A').is_well_formed :=
begin
  simp [anonomyous_experiment],

end

end anonomyous_experiment

section unforgeable_experiment

-- TODO: A also needs a corruption oracle for this experiment
def unforgeable_experiment (n : ℕ)
  (A : vector PK n → signing_oracle_comp rs n (M × Σ (l : ℕ), vector PK l × S l)) : 
  comp bool :=
(comp.vector_call (rs.gen) n).bind (λ ks, begin
  let pks := vector.map prod.fst ks,
  let sks := vector.map prod.snd ks,
  refine comp.bind ((A pks).simulate ks) (λ A_out, _),
  let m : M := A_out.1,
  let l : ℕ := A_out.2.1,
  let R : vector PK l := A_out.2.2.1,
  -- TODO: `R` should be a subset of `pks` - corrupted parties
  -- TODO: Adversary can't previously have queried Osign(*, m, R)
  let σ : S l := A_out.2.2.2,
  exact comp.ret (rs.verify l R m σ),
end)

@[simp]
instance unforgeable_experiment.is_well_formed (n : ℕ)
  (A : vector PK n → signing_oracle_comp rs n (M × Σ (l : ℕ), vector PK l × S l))
  [hA : ∀ pks, (A pks).is_well_formed] :
  (unforgeable_experiment rs n A).is_well_formed :=
by simp [unforgeable_experiment]

end unforgeable_experiment

end ring_sig

structure ring_signature_scheme (M : Type) (S : ℕ → ℕ → Type) (PK SK : ℕ → Type)
  [∀ sp, decidable_eq $ PK sp] :=
(rs (sp : ℕ) : ring_sig M (S sp) (PK sp) (SK sp))
(gen_poly_time : complexity_class.poly_time_comp₀ (λ sp, (rs sp).gen))
(sign_poly_time : false)
(verify_poly_time : false)

namespace ring_signature_scheme

open ring_sig

variables {M : Type} {S : ℕ → ℕ → Type} {PK SK : ℕ → Type}
variables [∀ sp, decidable_eq $ PK sp]
variable (rss : ring_signature_scheme M S PK SK)

-- TODO: Require `A` and `A'` have some poly_time hypothesis
def anonomyous := ∀ (p : polynomial ℕ)
  (A : Π sp, vector (PK sp) (p.eval sp) → signing_oracle_comp (rss.rs sp) (p.eval sp)
        (Σ (l : ℕ), M × (fin (p.eval sp) × fin l) × (fin (p.eval sp) × fin l) × (vector (PK sp) l)))
  
  (A' : Π sp, vector (PK sp × SK sp) (p.eval sp) → (Σ (l : ℕ), S sp l) 
    → signing_oracle_comp (rss.rs sp) (p.eval sp) bool)
   [hA' : ∀ sp ks σ, (A' sp ks σ).is_well_formed]
  [htA : ∀ sp pks, (A sp pks).is_well_formed]
  (A_poly_time : true) (A'_poly_time : true)
  ,
asymptotics.negligable (λ sp, begin
  -- let n : ℕ := p.eval sp,
  haveI : (anonomyous_experiment (rss.rs sp) (p.eval sp) (A sp) (A' sp)).is_well_formed := begin
    haveI := htA,
    refine anonomyous_experiment.is_well_formed _ _ _ _,
  end,
  -- -- haveI := hA,
  exact comp.Pr (anonomyous_experiment (rss.rs sp) (p.eval sp) (A sp) (A' sp)) - 0.5,
end)

def unforgeable := ∀ (p : polynomial ℕ)
  (A : Π sp, vector (PK sp) (p.eval sp) → 
    signing_oracle_comp (rss.rs sp) (p.eval sp) (M × Σ (l : ℕ), vector (PK sp) l × S sp l))
  [hA : ∀ sp pks, (A sp pks).is_well_formed]
  (A_poly_time : true),
asymptotics.negligable (λ sp, begin
  haveI := hA,
  exact comp.Pr (unforgeable_experiment (rss.rs sp) (p.eval sp) (A sp)),
end)

end ring_signature_scheme