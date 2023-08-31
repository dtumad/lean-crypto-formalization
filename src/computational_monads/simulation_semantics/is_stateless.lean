/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_tracking

/-!
# Tracking Simulation Oracles

This file defines a typeclass `sim_oracle.is_stateless` for oracles in which there is no
meaningful internal state, represented by the state type being `subsingleton`.
In theory we could take the state to be `unique` instead, but `subingleton` is usually simpler
since we already have `so.default_state` as an explicit element.

This is a special case of `sim_oracle.is_tracking`, see `is_stateless.is_tracking`.
This allows for a number of very general lemmas that simplify the process of working
with simulated computations, by automatically removing states.
We also construct a `stateless_oracle` that creates a simulation oracle from a direct specification
of a `query_f`, taking the state to be `unit` as a simple `subsingleton` type.

-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

open_locale big_operators ennreal
open oracle_comp oracle_spec

namespace sim_oracle

/-- Class to represent oracles that make no use of their internal state.
This class is introduced rather than using a `subsingleton` hypothesis directly
in order to create a unified `is_tracking` instance based on this fact.
This also allows typeclass resolution to work "backwords", in that subsingleton instances don't
have to be defined on the type parameter `S` explicitly, but on the actual oracle instead. -/
class is_stateless (so : sim_oracle spec spec' S) :=
(state_subsingleton : subsingleton S)

variables (so : sim_oracle spec spec' S) (i : spec.ι)
  (t t' : spec.domain i) (s s' : S) (u u' : spec.range i)

/-- Specialize `subsingleton.elim` to simplify the state to the default oracle state.
Usefull for giving a unified convergence point for state values. -/
@[simp] lemma state_elim [hso : so.is_stateless] (s : S) : s = so.default_state :=
@subsingleton.elim S hso.state_subsingleton s so.default_state

instance is_stateless.is_tracking [hso : so.is_stateless] : so.is_tracking :=
{ query_f := λ i t, prod.fst <$> so i (t, so.default_state),
  state_f := λ s i t u, so.default_state,
  apply_dist_equiv_state_f_map_query_f :=
    begin
      refine λ i t s, trans (trans (map_id_dist_equiv _).symm _) (map_comp_dist_equiv _ _ _).symm,
      refine map_dist_equiv_of_dist_equiv' (funext (λ x, prod.eq_iff_fst_eq_snd_eq.2
        ⟨rfl, state_elim so x.2⟩)) (by rw [state_elim so s]),
    end }

namespace is_stateless

@[simp] lemma answer_query_eq_map_apply [so.is_stateless] :
  so.answer_query i t = prod.fst <$> so i (t, so.default_state) := rfl

@[simp] lemma update_state_eq_const [so.is_stateless] :
  so.update_state s i t u = so.default_state := rfl

end is_stateless

end sim_oracle


/-- Simulate a computation without making use of the internal state.
  We use the `unit` type as the state in this case, so all possible states are equal.
  Implemented as a `tracking_oracle` where the state isn't actually tracking anything -/
def stateless_oracle (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)) :
  sim_oracle spec spec' unit :=
⟪o | λ _ _ _ _, (), ()⟫

notation `⟪` o `⟫` := stateless_oracle o

variable (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
variable   (o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i))


instance stateless_oracle.is_stateless : ⟪o⟫.is_stateless := sorry

namespace stateless_oracle

open sim_oracle

variables (oa : oracle_comp spec α)
  (i : spec.ι) (t : spec.domain i) (s s' : unit) (u : spec.range i)
  (x : spec.domain i × unit) (y : spec.range i × unit)

@[simp] lemma apply_eq : ⟪o⟫ i x = o i x.1 >>= λ u, return (u, ()) := by {cases x, refl}

@[pairwise_dist_equiv] lemma answer_query_dist_equiv : ⟪o⟫.answer_query i t ≃ₚ o i t :=
by rw_dist_equiv [map_bind_dist_equiv, map_return_dist_equiv, bind_return_id_dist_equiv]

lemma update_query_eq : ⟪o⟫.update_state s i t u = () := rfl

lemma simulate_eq_default_simulate : simulate ⟪o⟫ oa s = default_simulate ⟪o⟫ oa :=
simulate_eq_default_simulate ⟪o⟫ oa s

lemma simulate'_eq_default_simulate' : simulate' ⟪o⟫ oa s = default_simulate' ⟪o⟫ oa :=
simulate'_eq_default_simulate' ⟪o⟫ oa s

section support

lemma support_apply : (⟪o⟫ i x).support = prod.fst ⁻¹' (o i x.1).support :=
by simp only [apply_eq, support_bind_prod_mk_of_snd_subsingleton, set.image_id']

lemma mem_support_apply_iff : y ∈ (⟪o⟫ i (t, s)).support ↔ y.1 ∈ (o i t).support :=
by cases y; simp only [apply_eq, support_bind, support_return, set.mem_Union, prod.mk.inj_iff,
  set.mem_singleton_iff, eq_iff_true_of_subsingleton, and_true, exists_prop, exists_eq_right']

/-- The `support` of `simulate` is the preimage of the support of `simulate'`,
as there is only one possible internal state for the oracle. -/
lemma support_simulate_eq_preimage_support_simulate' :
  (simulate ⟪o⟫ oa s).support = prod.fst ⁻¹' (simulate' ⟪o⟫ oa ()).support :=
support_simulate_eq_preimage_support_simulate' ⟪o⟫ oa s

/-- If the oracle function can take on any possible output, simulation doesn't affect `support`. -/
lemma support_simulate'_eq_support (h : ∀ i t, (o i t).support = set.univ) :
  (simulate' ⟪o⟫ oa s).support = oa.support :=
sim_oracle.is_tracking.support_simulate'_eq_support _ oa s begin
  -- intros i t,
  refine λ i t, (answer_query_dist_equiv o i t).support_eq.trans (h i t)
end

lemma support_simulate_eq_preimage_support (h : ∀ i t, (o i t).support = ⊤) :
  (simulate ⟪o⟫ oa s).support = prod.fst ⁻¹' oa.support :=
sorry
-- tracking_oracle.support_simulate_eq_preimage_support_of_subsingleton o _ _ oa s h

lemma support_simulate'_eq_support_simulate' (h : ∀ i t, (o i t).support = (o' i t).support) :
  (simulate' ⟪o⟫ oa s).support = (simulate' ⟪o'⟫ oa s').support :=
sorry --tracking_oracle.support_simulate'_eq_support_simulate' o o' _ _ () () oa s s' h

lemma support_simulate_eq_support_simulate (h : ∀ i t, (o i t).support = (o' i t).support) :
  (simulate ⟪o⟫ oa s).support = (simulate ⟪o'⟫ oa s').support :=
support_simulate_eq_support_simulate_of_subsingleton oa ⟪o⟫ ⟪o'⟫ s s'
  (λ i t, by rw [support_apply, support_apply, h])

@[simp] lemma mem_support_simulate_iff (y : α × unit) :
  y ∈ (simulate ⟪o⟫ oa s).support ↔ y.1 ∈ (simulate' ⟪o⟫ oa ()).support :=
by rw [support_simulate_eq_preimage_support_simulate', set.mem_preimage]

end support

section fin_support

-- TODO: this should generalize I think?
lemma fin_support_apply : (⟪o⟫ i x).fin_support = finset.preimage (o i t).fin_support prod.fst
  (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨h, punit_eq _ _⟩) :=
sorry

lemma mem_fin_support_apply : y ∈ (⟪o⟫ i x).fin_support ↔ y.1 ∈ (o i x.1).fin_support :=
sorry

end fin_support

section eval_dist

lemma eval_dist_apply : ⁅⟪o⟫ i x⁆ = ⁅o i x.1⁆.map (λ u, (u, ())) :=
by rw [apply_eq, eval_dist_bind_return]

/-- If the oracle responds uniformly to queries, then simulation doesn't affect `eval_dist`. -/
lemma eval_dist_simulate'_eq_eval_dist
  (h : ∀ i t, ⁅o i t⁆ = pmf.uniform_of_fintype (spec.range i)) : ⁅simulate' ⟪o⟫ oa s⁆ = ⁅oa⁆ :=
sorry --tracking_oracle.eval_dist_simulate'_eq_eval_dist o _ _ oa s h

lemma eval_dist_simulate'_eq_eval_dist_simulate' (h : ∀ i t, ⁅o i t⁆ = ⁅o' i t⁆) :
  ⁅simulate' ⟪o⟫ oa s⁆ = ⁅simulate' ⟪o'⟫ oa s'⁆ :=
sorry --tracking_oracle.eval_dist_simulate'_eq_eval_dist_simulate' o o' _ _ _ _ oa s s' h

/-- The `eval_dist` of `simulate` is the result of mapping the `eval_dist` of `simulate'`
under the map adding on a default `()` value for the internal state. -/
lemma eval_dist_simulate_eq_map_eval_dist_simulate' :
  ⁅simulate ⟪o⟫ oa s⁆ = ⁅simulate' ⟪o⟫ oa s⁆.map (λ x, (x, ())) :=
by simp only [eval_dist_simulate_eq_map_eval_dist_simulate'_of_subsingleton, punit_eq s ()]

lemma eval_dist_simulate_eq_eval_dist_simulate (h : ∀ i t, ⁅o i t⁆ = ⁅o' i t⁆) :
  ⁅simulate ⟪o⟫ oa s⁆ = ⁅simulate ⟪o'⟫ oa s'⁆ :=
sorry -- by simp only [eval_dist_simulate_eq_map_eval_dist_simulate',
--   eval_dist_simulate'_eq_eval_dist_simulate' oa o o' s s' h]

lemma eval_dist_simulate_apply_eq_eval_dist_simulate'_apply (x : α × unit) :
  ⁅simulate ⟪o⟫ oa s⁆ x = ⁅simulate' ⟪o⟫ oa s⁆ x.1 :=
prob_output_simulate_eq_prob_output_simulate'_of_subsingleton ⟪o⟫ oa s x

end eval_dist

section prob_event

lemma prob_event_apply (e : set $ spec.range i × unit) :
  ⁅e | ⟪o⟫ i x⁆ = ⁅(λ x, (x, ())) ⁻¹' e | o i x.1⁆ :=
by rw [apply_eq, prob_event_bind_return]

/-- If the oracle function responds uniformly, then simulation doesn't affect `prob_event`. -/
lemma prob_event_simulate'_eq_prob_event
  (h : ∀ i t, ⁅o i t⁆ = pmf.uniform_of_fintype (spec.range i)) (e : set α) :
  ⁅e | simulate' ⟪o⟫ oa s⁆ = ⁅e | oa⁆ :=
sorry --prob_event_eq_of_eval_dist_eq (eval_dist_simulate'_eq_eval_dist oa o s h) e

lemma prob_event_simulate'_eq_prob_event_simulate' (h : ∀ i t, ⁅o i t⁆ = ⁅o' i t⁆) (e : set α) :
  ⁅e | simulate' ⟪o⟫ oa s⁆ = ⁅e | simulate' ⟪o'⟫ oa s'⁆ :=
sorry --prob_event_eq_of_eval_dist_eq (eval_dist_simulate'_eq_eval_dist_simulate' oa o o' s s' h) e

lemma prob_event_simulate (e : set $ α × unit) :
  ⁅e | simulate ⟪o⟫ oa s⁆ = ⁅prod.fst '' e | simulate' ⟪o⟫ oa s⁆ :=
begin
  sorry
end

end prob_event

end stateless_oracle

-- More lemmas we can prove about `tracking_oracle` with the definition of the `stateless_oracle`
namespace tracking_oracle


-- variables (oa : oracle_comp spec α)
--   (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
--   (o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i))
--   (i : spec.ι) (t : spec.domain i) (s s' : unit) (u : spec.range i)
--   (x : spec.domain i × unit) (y : spec.range i × unit)


variables
  (update_state update_state': Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state default_state' s s' : S) (oa : oracle_comp spec α)

section support

/-- The first output with a tracking oracle is independent of any of the tracking state -/
lemma support_simulate'_eq_support_simulate'_stateless_oracle :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support = (simulate' ⟪o⟫ oa ()).support :=
begin
  sorry
  -- unfold stateless_oracle,
  -- refine support_simulate'_eq_of_oracle_eq o update_state (λ _ _ _ _, ()) default_state _ oa s _
end

end support

section distribution_semantics

/-- The first output of a tracking oracle is equivalent to using just the stateless oracle -/
lemma simulate'_equiv_stateless_oracle :
  simulate' ⟪o | update_state, default_state⟫ oa s ≃ₚ simulate' ⟪o⟫ oa () :=
begin
  sorry
  -- induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  -- { simp },
  -- { let so := ⟪o|update_state, default_state⟫,
  --   calc simulate' so (oa >>= ob) s
  --     ≃ₚ (simulate so oa s) >>= (λ x, simulate' so (ob x.1) x.2) :
              --simulate'_bind_equiv so oa ob s
  --     ... ≃ₚ (simulate so oa s) >>= (λ x, simulate' ⟪o⟫ (ob x.1) ()) :
  --       bind_equiv_of_equiv_second _ (λ a, (hob a.1 a.2))
  --     ... ≃ₚ (simulate' so oa s) >>= (λ x, simulate' ⟪o⟫ (ob x) ()) : by erw [bind_map_equiv]
  --     ... ≃ₚ (simulate' ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x) ()) :
  --       bind_equiv_of_equiv_first _ (hoa _)
  --     ... ≃ₚ (simulate ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x.1) ()) : by erw [bind_map_equiv]
  --     ... ≃ₚ (simulate ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x.1) x.2) :
  --       by { congr, ext x, rw [punit_eq () x.2] }
  --     ... ≃ₚ simulate' ⟪o⟫ (oa >>= ob) () : by rw [simulate'_bind_equiv] },
  -- { simp_rw [simulate'_query_equiv, apply_eq, stateless_oracle.apply_eq, map_bind_equiv],
  --   refine bind_equiv_of_equiv_second (o i t) _,
  --   simp only [map_pure_equiv, eq_self_iff_true, forall_const] }
end

/-- The first ouptput of a tracking oracle is indepenedent of the actual tracking functions
TODO: `so.answer_query i t ≃ₚ so'.answer_query i t` -/
lemma simulate'_equiv_of_equiv (h : ∀ i t, o i t ≃ₚ o' i t) :
  simulate' ⟪o | update_state, default_state⟫ oa s ≃ₚ
    simulate' ⟪o' | update_state', default_state'⟫ oa s' :=
calc simulate' ⟪o | update_state, default_state⟫ oa s
  ≃ₚ simulate' ⟪o⟫ oa () : simulate'_equiv_stateless_oracle o update_state default_state s oa
  ... ≃ₚ simulate' ⟪o'⟫ oa () :
    stateless_oracle.eval_dist_simulate'_eq_eval_dist_simulate' _ _ _ _ _ h
  ... ≃ₚ simulate' ⟪o' | update_state', default_state'⟫ oa s' :
    symm (simulate'_equiv_stateless_oracle o' update_state' default_state' _ _)

end distribution_semantics

end tracking_oracle