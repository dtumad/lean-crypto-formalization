/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_stateless

/-!
# Uniform Oracles

This file defines a simulation oracle called `uniformₛₒ` that reduces any computation to
one with only a `unif_spec` oracle by responding uniformly at random to any query.
Because of the way `eval_dist` is defined this doesn't change the associated distribution,
only the representation in terms of oracles available.
The main use case is in later defining random oracles (see `randomₛₒ`).
-/

open oracle_comp oracle_spec sim_oracle prod

variables {α β : Type} {spec : oracle_spec}

noncomputable def uniform_oracle (spec : oracle_spec) : sim_oracle spec unif_spec unit :=
λ i z, do {u ← $ᵗ (spec.range i), return (u, ())}

notation `uniformₛₒ` := uniform_oracle _

instance uniform_oracle.is_stateless : (uniform_oracle spec).is_stateless :=
{ state_subsingleton := punit.subsingleton }

namespace uniform_oracle

lemma apply_eq {i : spec.ι} (t : spec.domain i) (s : unit) :
  uniformₛₒ i (t, s) = do {u ← $ᵗ (spec.range i), return (u, ())} := rfl

section simulate'

variables (oa : oracle_comp spec α) (s : unit)

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' uniformₛₒ oa s ≃ₚ oa :=
begin 
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { rw [simulate'_return, map_return, return_dist_equiv_return_iff'] },
  { simp_rw [simulate'_bind, simulate_query, apply_eq, bind_assoc, return_bind],
    refine bind_dist_equiv_bind_of_dist_equiv _ (λ _ _, _); pairwise_dist_equiv [hoa] }
end

@[simp] lemma support_simulate' : (simulate' uniformₛₒ oa s).support = oa.support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_simulate' [decidable_eq α] :
  (simulate' uniformₛₒ oa s).fin_support = oa.fin_support :=
by pairwise_dist_equiv

@[simp] lemma eval_dist_simulate' : ⁅simulate' uniformₛₒ oa s⁆ = ⁅oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_output_simulate' (x : α) : ⁅= x | simulate' uniformₛₒ oa s⁆ = ⁅= x | oa⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_simulate' (e : set α) : ⁅e | simulate' uniformₛₒ oa s⁆ = ⁅e | oa⁆ :=
by pairwise_dist_equiv

end simulate'

section simulate

variables (oa : oracle_comp spec α) (s : unit)

@[pairwise_dist_equiv] lemma simulate_dist_equiv :
  simulate uniformₛₒ oa s ≃ₚ do {x ← oa, return (x, ())} :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { rw [simulate_return, return_bind, punit_eq s ()],
    exact return_dist_equiv_return _ _ _ },
  { simp_rw [simulate_bind, simulate_query, apply_eq, bind_assoc, return_bind],
    refine bind_dist_equiv_bind_of_dist_equiv _ (λ _ _, _); pairwise_dist_equiv [hoa] }
end

-- is_stateless.simulate_dist_equiv_self uniformₛₒ oa s
--   (λ i t, by rw_dist_equiv [stateless_oracle.answer_query_dist_equiv,
--     uniform_select_fintype_range t])

-- @[simp] lemma support_simulate : (simulate uniformₛₒ oa s).support = oa.support ×ˢ {()} :=
-- is_stateless.support_simulate_eq_support uniformₛₒ oa s (by simp)

-- @[simp] lemma fin_support_simulate [decidable_eq α] :
--   (simulate uniformₛₒ oa s).fin_support = oa.fin_support ×ˢ {()} :=
-- is_stateless.fin_support_simulate_eq_fin_support uniformₛₒ oa s (by simp)

-- @[simp] lemma eval_dist_simulate : ⁅simulate uniformₛₒ oa s⁆ = ⁅oa ×ₘ return ()⁆ :=
-- is_stateless.eval_dist_simulate_eq_eval_dist uniformₛₒ oa s (by simp)

-- @[simp] lemma prob_output_simulate (z : α × unit) : ⁅= z | simulate uniformₛₒ oa s⁆ = ⁅= z.1 | oa⁆ :=
-- is_stateless.prob_output_simulate_eq_prob_output uniformₛₒ oa s (by simp [prob_output_query_eq_inv]) z

-- @[simp] lemma prob_event_simulate (e : set (α × unit)) :
--   ⁅e | simulate uniformₛₒ oa s⁆ = ⁅fst '' e | oa⁆ :=
-- is_stateless.prob_event_simulate_eq_prob_event uniformₛₒ oa s (by simp [prob_output_query_eq_inv]) e

end simulate

end uniform_oracle