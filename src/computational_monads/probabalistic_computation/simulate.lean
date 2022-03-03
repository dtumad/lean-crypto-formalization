import data.bitvec.basic
import computational_monads.probabalistic_computation.prob_alg

namespace prob_alg

section decidable

-- #check decidable_eq

inductive decidable' : Π {A : Type} (ca : prob_alg A), Type 1
| decidable_pure' {A : Type} (hA : decidable_eq A) (a : A) : decidable' (pure' A a)
| decidable_bind' {A B : Type} (ca : prob_alg A) (cb : A → prob_alg B)
    (hca : decidable' ca) (hcb : ∀ a, decidable' (cb a)) : decidable' (bind' A B ca cb)
| decidable_coin : decidable' coin
| decidable_repeat {A : Type} (ca : prob_alg A) (p : A → Prop)
    (hca : decidable' ca) (hp : decidable_pred p) : decidable' (repeat ca p)

def decidable : Π {A : Type} (ca : prob_alg A), Sort 1
| _ (pure' A a) := decidable_eq A
| _ (bind' A B ca cb) := decidable ca × Π a, decidable (cb a)
| _ coin := unit
| A (repeat ca p) := decidable ca × decidable_pred p

def decidable_eq_of_prob_alg : Π {A : Type} (ca : prob_alg A) (hca : decidable ca), decidable_eq A
| _ (pure' A a) h := h
| _ (bind' A B ca cb) h := let ⟨a⟩ := inhabited_of_prob_alg ca
  in decidable_eq_of_prob_alg (cb a) (h.2 a)
| _ coin _ := bool.decidable_eq
| A (repeat ca p) h := decidable_eq_of_prob_alg ca h.1



end decidable

open decidable'

section partial_simulate

-- def simulate_step : Π {A : Type} (ca : prob_alg A) (b : bool), 

/-- The result of simulation is either a value and a list of remaining random coins,
  or a `prob_comp` representing the remaining computation after running out of random coins -/
-- def simulation_result (A : Type) := (A × list bool) ⊕ prob_alg A

inductive simulation_result (A : Type) : Type 1
| done (result : A) : simulation_result
| more (ca : prob_alg A) (hca : decidable' ca) : simulation_result

def step : Π {A : Type} (ca : prob_alg A) (h : decidable' ca) (b : bool), simulation_result A
| _ (pure' A a) (decidable_pure' _ _) seed := simulation_result.done a
| _ (bind' A B _ _) (decidable_bind' ca cb hca hcb) seed := match step ca hca seed with
  | simulation_result.done a := simulation_result.more (cb a) (hcb a)
  | simulation_result.more ca' hca' := simulation_result.more (ca' >>= cb) (decidable_bind' ca' cb hca' hcb)
end
| _ coin _ b := simulation_result.done b
| A (repeat _ _) (decidable_repeat ca p hca hp) seed := 
  by haveI : decidable_pred p := hp; exact (simulation_result.more (do {
  a ← ca, x ← if p a then return a else repeat ca p, return x
}) (decidable_bind' ca _ hca (λ a, decidable_bind' _ _ (sorry) (λ _, sorry))))

def steps : Π {A : Type} (ca : prob_alg A) (h : decidable' ca) (seed : list bool), simulation_result A
| A ca h [] := simulation_result.more ca h
| A ca h (x :: xs) := match step ca h x with
  | simulation_result.done a := simulation_result.done a
  | simulation_result.more ca' hca' := steps ca' hca' xs
end

-- /-- Small-step semantics for simulating a `prob_alg` from a set of predetermined coin flips.
--   Decidabilty of the `prob_alg` is needed to -/
-- def partial_simulate : Π {A : Type} (ca : prob_alg A) (h : decidable' ca)
--   (seed : list bool), simulation_result A
-- | _ (pure' A a) (decidable_pure' _ _) seed := sum.inl ⟨a, seed⟩
-- | _ (bind' A B ca cb) h seed := match partial_simulate ca sorry seed with
--   | sum.inl ⟨a, seed'⟩ := partial_simulate (cb a) sorry seed'
--   | sum.inr ca' := sum.inr (ca' >>= cb)
-- end
-- | _ coin _ (b :: seed) := sum.inl ⟨b, seed⟩
-- | _ coin _ [] := sum.inr coin
-- | A (repeat ca p) h seed :=
--   by haveI : decidable_pred p := sorry; exact
--   match partial_simulate ca sorry seed with
--   | sum.inl ⟨a, seed'⟩ := if p a then sum.inl ⟨a, seed'⟩ else partial_simulate (repeat ca p) h seed'
--   | sum.inr ca' := begin 
--     exact sum.inr sorry
-- end
-- end

end partial_simulate

end prob_alg