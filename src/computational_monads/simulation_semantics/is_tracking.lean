/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.induction
import computational_monads.distribution_semantics.mprod

/-!
# Tracking Simulation Oracles

TODO: update all of this.

This file defines a typeclass `sim_oracle.is_tracking` for oracles in which the
query responses are independent of the current oracle state.
This is represented by giving functions `query_f` and `state_f` that correspond to these pieces,
and a statement `apply_dist_equiv_state_f_map_query_f` that shows that the oracle function
actually splits into the two components given.

Note that we require that `query_f` be deterministic for simplicity.
For current use cases this is generally sufficient.
Also note that because `query_f` and `state_f` are given explicitly rather than existentially,
`is_tracking` is not a proposition, and in particular two different instances may exist.
Generally it's best to avoid situations with multiple distinct instances.

For example in `loggingₛₒ` the internal state doesn't change the main output, it just records it.
This allows for many lemmas to be automatically shared between these sorts of oracles.

We also construct a `tracking_oracle` that creates a simulation oracle from a direct specification
of `query_f` and `state_f`, that satisfies `is_tracking` by construction.
This is convenient in defining e.g. `loggingₛₒ` and `idₛₒ`.

TODO: compatibility lemmas for oracle append and compose operations.
-/

open oracle_comp oracle_spec prod

variables {α β γ : Type} {spec : oracle_spec} {S S' : Type}

namespace sim_oracle

/-- Typeclass for simulation oracles that don't modify the query result,
but just use the internal state to track some aspect of the computation.
We assume exact equality rather than distributional equivalence for simplicity. -/
class is_tracking (so : sim_oracle spec spec S) :=
(fst_map_apply_eq_query' : ∀ (i : spec.ι) (t : spec.domain i) (s : S),
  fst <$> so i (t, s) = query i t)

namespace is_tracking

variables (so : sim_oracle spec spec S) [is_tracking so]
  (so' : sim_oracle spec spec S') 
  (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i) (s : S)

@[simp] lemma fst_map_apply_eq_query : fst <$> so i (t, s) = query i t :=
is_tracking.fst_map_apply_eq_query' i t s

@[pairwise_dist_equiv] lemma fst_map_apply_dist_equiv_query :
  fst <$> so i (t, s) ≃ₚ query i t := dist_equiv_of_eq (fst_map_apply_eq_query so i t s)

@[simp] lemma simulate'_eq_const :
  (simulate' so : oracle_comp spec α → S → oracle_comp spec α) = function.const S :=
begin
  refine funext (λ oa, funext (λ s, _)),
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { refl },
  { simp_rw [simulate'_bind, simulate_query, ← fst_map_apply_eq_query so i t s,
      oracle_comp.map_eq_bind_return_comp, bind_assoc, hoa, pure_bind] }
end

lemma simulate'_eq_self : simulate' so oa s = oa := by rw [simulate'_eq_const]

@[pairwise_dist_equiv] lemma simulate'_dist_equiv_self : simulate' so oa s ≃ₚ oa :=
by rw [simulate'_eq_self]

end is_tracking

end sim_oracle

/-- Simple oracle for keeping some internal state without modifying query behavior-/
def tracking_oracle (update_state : Π (i : spec.ι), spec.domain i → spec.range i → S → S) :
  sim_oracle spec spec S :=
λ i ⟨t, s⟩, do {u ← query i t, return (u, update_state i t u s)}

instance tracking_oracle.is_tracking
  (update_state : Π (i : spec.ι), spec.domain i → spec.range i → S → S):
  (tracking_oracle update_state).is_tracking :=
{ fst_map_apply_eq_query' := λ i t s, rfl }

namespace tracking_oracle

variables (update_state : Π (i : spec.ι), spec.domain i → spec.range i → S → S)

@[simp] lemma apply_eq (i : spec.ι) (z : spec.domain i × S) :
  tracking_oracle update_state i z = do {u ← query i z.1, return (u, update_state i z.1 u z.2)} :=
prod.rec_on z (λ t s, rfl)

end tracking_oracle