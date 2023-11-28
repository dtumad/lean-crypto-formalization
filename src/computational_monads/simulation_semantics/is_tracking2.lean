/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.subsingleton
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
`sim_oracle.is_stateless` extends this further to oracles with no internal state at all.

We also construct a `tracking_oracle` that creates a simulation oracle from a direct specification
of `query_f` and `state_f`, that satisfies `is_tracking` by construction.
This is convenient in defining e.g. `loggingₛₒ` and `idₛₒ`.

TODO: compatibility lemmas for oracle append and compose operations.
-/

open oracle_comp oracle_spec prod

variables {α β γ : Type} {spec : oracle_spec} {S : Type}

namespace sim_oracle

/-- Typeclass for simulation oracles that don't modify the query result,
but just do some -/
class is_tracking (so : sim_oracle spec spec S) :=
(fst_map_apply_eq_query' : ∀ (i : spec.ι) (t : spec.domain i) (s : S),
  fst <$> so i (t, s) = query i t)

namespace is_tracking

variables (so : sim_oracle spec spec S) [is_tracking so]

@[simp] lemma fst_map_apply_eq_query (i : spec.ι) (t : spec.domain i) (s : S) :
  fst <$> so i (t, s) = query i t := is_tracking.fst_map_apply_eq_query' i t s

@[pairwise_dist_equiv] lemma fst_map_apply_dist_equiv_query (i : spec.ι) (t : spec.domain i)
  (s : S) : fst <$> so i (t, s) ≃ₚ query i t := dist_equiv_of_eq (fst_map_apply_eq_query so i t s)

variables (oa : oracle_comp spec α) (s : S)

lemma simulate'_dist_equiv_self : simulate' so oa s ≃ₚ oa :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { refl },
  { rw_dist_equiv [simulate'_bind_dist_equiv, hoa, simulate_query_dist_equiv,
      (fst_map_apply_dist_equiv_query so i t s).symm, bind_map_dist_equiv] }
end

@[simp] lemma support_simulate' : (simulate' so oa s).support = oa.support :=
(simulate'_dist_equiv_self so oa s).support_eq

@[simp] lemma fin_support_simulate' [decidable_eq α] :
  (simulate' so oa s).fin_support = oa.fin_support :=
(simulate'_dist_equiv_self so oa s).fin_support_eq

@[simp] lemma eval_dist_simulate' : ⁅simulate' so oa s⁆ = ⁅oa⁆ :=
(simulate'_dist_equiv_self so oa s).eval_dist_eq

@[simp] lemma prob_output_simulate' (x : α) : ⁅= x | simulate' so oa s⁆ = ⁅= x | oa⁆ :=
(simulate'_dist_equiv_self so oa s).prob_output_eq x

@[simp] lemma prob_event_simulate' (e : set α) : ⁅e | simulate' so oa s⁆ = ⁅e | oa⁆ :=
(simulate'_dist_equiv_self so oa s).prob_event_eq e

end is_tracking

end sim_oracle

def tracking_oracle
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state : S) : sim_oracle spec spec S :=
{ default_state := default_state,
  o := λ i ⟨t, s⟩, do {u ← query i t, return (u, update_state s i t u)} }

notation `⟪query|` update_state `,` default_state `⟫` :=
tracking_oracle update_state default_state

instance tracking_oracle.is_tracking
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state : S) : (tracking_oracle update_state default_state).is_tracking :=
{ fst_map_apply_eq_query' := λ i t s, rfl }

namespace tracking_oracle


end tracking_oracle