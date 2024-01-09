/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.is_query_bound
import computational_monads.constructions.uniform_select

/-!
# Uniform Oracles

This file defines a simulation oracle called `uniformₛₒ` that reduces any computation to
one with only a `unif_spec` oracle by responding uniformly at random to any query.
Because of the way `eval_dist` is defined this doesn't change the associated distribution,
only the representation in terms of oracles available.
The main use case is in later defining random oracles (see `randomₛₒ`).
-/

open oracle_comp oracle_spec sim_oracle prod

noncomputable def uniform_oracle (spec : oracle_spec) : sim_oracle spec unif_spec unit :=
λ i z, do {u ← $ᵗ (spec.range i), return (u, ())}

notation `uniformₛₒ` := uniform_oracle _

namespace uniform_oracle

variables {spec : oracle_spec} {α β : Type}

section apply

lemma apply_eq {i : spec.ι} (t : spec.domain i) (s : unit) :
  uniformₛₒ i (t, s) = do {u ← $ᵗ (spec.range i), return (u, ())} := rfl

end apply

section simulate'

variables (oa : oracle_comp spec α) (s : unit)

@[pairwise_dist_equiv] lemma simulate'_dist_equiv : simulate' uniformₛₒ oa s ≃ₚ oa :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { exact return_dist_equiv_return _ _ a },
  { simp_rw [simulate'_bind, simulate_query, apply_eq, bind_assoc, oracle_comp.return_bind],
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
  { rw [simulate_return, oracle_comp.return_bind, punit_eq s ()],
    exact return_dist_equiv_return _ _ _ },
  { simp_rw [simulate_bind, simulate_query, apply_eq, bind_assoc, oracle_comp.return_bind],
    refine bind_dist_equiv_bind_of_dist_equiv _ (λ _ _, _); pairwise_dist_equiv [hoa] }
end

@[simp] lemma support_simulate :
  (simulate uniformₛₒ oa s).support = (λ x, (x, ())) '' oa.support :=
(simulate_dist_equiv oa s).support_eq.trans (support_bind_return _ _)

@[simp] lemma fin_support_simulate [decidable_eq α] :
  (simulate uniformₛₒ oa s).fin_support = oa.fin_support.image (λ x, (x, ())) :=
(simulate_dist_equiv oa s).fin_support_eq.trans (fin_support_bind_return _ _)

@[simp] lemma eval_dist_simulate : ⁅simulate uniformₛₒ oa s⁆ = ⁅oa⁆.map (λ x, (x, ())) :=
(simulate_dist_equiv oa s).eval_dist_eq.trans (eval_dist_bind_return _ _)

@[simp] lemma prob_output_simulate (z : α × unit) :
  ⁅= z | simulate uniformₛₒ oa s⁆ = ⁅= z.1 | oa⁆ :=
begin
  refine ((simulate_dist_equiv oa s).prob_output_eq z).trans _,
  simp only [prob_output_bind_prod_mk_fst, id_map', prob_output_return,
    eq_iff_true_of_subsingleton, if_true, mul_one]
end

@[simp] lemma prob_event_simulate (e : set (α × unit)) :
  ⁅e | simulate uniformₛₒ oa s⁆ = ⁅fst '' e | oa⁆ :=
begin
  refine ((simulate_dist_equiv oa s).prob_event_eq e).trans _,
  simpa only [prob_event_bind_return, set.preimage, set.image, exists_and_distrib_right,
    exists_eq_right, prod.exists, unique.exists_iff],
end

end simulate

end uniform_oracle