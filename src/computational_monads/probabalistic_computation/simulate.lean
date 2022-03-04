import data.bitvec.basic
import computational_monads.probabalistic_computation.constructions

namespace prob_alg

variables {A B : Type} (ca : prob_comp A)

open decidable_alg

/-- The result of simulation is either a value and a list of remaining random coins,
  or a `prob_comp` representing the remaining computation after running out of random coins -/
inductive simulation_result (A : Type) : Type 1
| done (result : A) : simulation_result
| done_unused (result : A) (b : bool) : simulation_result
| more (ca : prob_alg A) (hca : decidable_alg ca) : simulation_result

namespace simulation_result

def to_prob_comp (sa : simulation_result A) : prob_alg A :=
match sa with
| (done a) := return a
| (done_unused a b) := return a
| (more ca hca) := ca
end

def to_prob_comp_decidable (A : Type) [hA : decidable_eq A] (sa : simulation_result A) :
  (sa.to_prob_comp).decidable_alg :=
match sa with
| (done a) := decidable_pure' hA a
| (done_unused a b) := decidable_pure' hA a
| (more ca hca) := hca
end

end simulation_result

/-- Single simulation step used to build up the actual simulation.
  If the step computes a value without using the given bit it will return it back -/
def simulate_step : Π {A : Type} (ca : prob_alg A) (h : decidable_alg ca) (b : bool), simulation_result A
| _ coin _ b := simulation_result.done b
| _ (pure' A a) h seed := simulation_result.done_unused a seed
| _ (bind' A B _ _) (decidable_bind' ca cb hca hcb) seed := match simulate_step ca hca seed with
  -- If we use the bit and compute a value, then suspend at the binding operation
  | simulation_result.done a := simulation_result.more (cb a) (hcb a)
  -- If we never used the bit we can continuse simulating the next branch in this step
  | simulation_result.done_unused a seed' := simulate_step (cb a) (hcb a) seed'
  -- If we used the bit without completing, store our current place in a `more`
  | simulation_result.more ca' hca' := simulation_result.more (ca' >>= cb) (decidable_bind' _ _ hca' hcb)
end
| A (repeat _ _) (decidable_repeat ca p hca hp) seed := begin
  haveI : decidable_pred p := hp,
  haveI hA : decidable_eq A := decidable_eq_of_decidable_alg ca hca,
  exact match simulate_step ca hca seed with
  | (simulation_result.done a) := if p a then simulation_result.done a
      else simulation_result.more (repeat ca p) (decidable_repeat ca p hca hp)
  -- `p a` must hold if we are in this case (assuming the original computation is well-formed)
  | (simulation_result.done_unused a b) := if p a then simulation_result.done_unused a b
      else simulation_result.more (repeat ca p) (decidable_repeat ca p hca hp)
  -- If the computation partially finishes, then unroll a single loop iteration
  | (simulation_result.more ca' hca') := simulation_result.more
      (do { a ← ca', x ← if p a then return a else repeat ca p, return x })
      (by { refine decidable_bind' _ _ hca' (λ a, decidable_bind' _ _ _ (λ x, decidable_pure' hA x)),
        split_ifs, exact (decidable_pure' hA a), exact (decidable_repeat ca p hca hp) })
  end,
end

lemma simulate_step_eq_done_unused_iff {A : Type} (ca : prob_comp A)
  (h : decidable_alg ca.alg) (b b' : bool) (a : A) :
  simulate_step ca.alg h b = simulation_result.done_unused a b' ↔
    ⟦ca⟧ᵖ a = 1 ∧ b = b' :=
sorry
    

/-- Small-step semantics for simulating a `prob_alg` from a set of predetermined coin flips.
  Decidabilty of the `prob_alg` is needed to -/
def simulate : Π {A : Type} (ca : prob_alg A) (h : decidable_alg ca) (seed : list bool), simulation_result A
| A ca h [] := simulation_result.more ca h
| A ca h (x :: xs) := match simulate_step ca h x with
  | simulation_result.done a := simulation_result.done a
  | simulation_result.done_unused a b := simulation_result.done_unused a b
  | simulation_result.more ca' hca' := simulate ca' hca' xs
end

lemma simulate_well_formed {A : Type} (ca : prob_comp A) (h : decidable_alg ca.alg) (seed : list bool) :
  well_formed (simulation_result.to_prob_comp (simulate ca.alg h seed)) :=
sorry

lemma simulate_correct {A : Type} (ca : prob_comp A) (h : decidable_alg ca.alg) :
  ∃ (n₀ : ℕ), ∀ n, n > n₀ → ⟦ca⟧ᵖ = ⟦do {
    v ← prob_comp.vector_call ⟨coin, coin_well_formed⟩ n,
    ⟨simulation_result.to_prob_comp (simulate ca.alg h v.to_list), simulate_well_formed ca h v.to_list⟩
  }⟧ᵖ :=
sorry

end prob_alg