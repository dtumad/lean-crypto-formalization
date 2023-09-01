/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_tracking
import computational_monads.distribution_semantics.mprod
import computational_monads.distribution_semantics.subsingleton

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

open_locale big_operators ennreal
open oracle_comp oracle_spec sim_oracle

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace sim_oracle

/-- Class to represent oracles that make no use of their internal state.
This class is introduced rather than using a `subsingleton` hypothesis directly
in order to create a unified `is_tracking` instance based on this fact.
This also allows typeclass resolution to work "backwords", in that subsingleton instances don't
have to be defined on the type parameter `S` explicitly, but on the actual oracle instead. -/
class is_stateless (so : sim_oracle spec spec' S) : Prop :=
(state_subsingleton : subsingleton S)

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S)

/-- Specialize `subsingleton.elim` to simplify the state to the default oracle state.
Usefull for giving a unified convergence point for state values. -/
lemma is_stateless.state_elim [hso : so.is_stateless] (s : S) : s = so.default_state :=
@subsingleton.elim S hso.state_subsingleton s so.default_state

lemma is_stateless.state_elim' [hso : so.is_stateless] (s s' : S) : s = s' :=
@subsingleton.elim S hso.state_subsingleton s s'

@[simp] lemma default_state_eq_iff_true [so.is_stateless] (s : S) : so.default_state = s ↔ true :=
by rw [is_stateless.state_elim so s, eq_self_iff_true]

@[simp] lemma eq_default_state_iff_true [so.is_stateless] (s : S) : s = so.default_state ↔ true :=
by rw [is_stateless.state_elim so s, eq_self_iff_true]

/-- Because of `so.default_state`, the fact that `S` is `subsingleton` implies it is `unique`. -/
def is_stateless.state_unique [hso : so.is_stateless] : unique S :=
{ default := so.default_state,
  uniq := λ s, is_stateless.state_elim' so _ _}

instance is_stateless.is_tracking [hso : so.is_stateless] : so.is_tracking :=
{ query_f := λ i t, prod.fst <$> so i (t, so.default_state),
  state_f := λ s i t u, so.default_state,
  apply_dist_equiv_state_f_map_query_f :=
    begin
      refine λ i t s, trans (trans (map_id_dist_equiv _).symm _) (map_comp_dist_equiv _ _ _).symm,
      refine map_dist_equiv_of_dist_equiv' (funext (λ x, prod.eq_iff_fst_eq_snd_eq.2
        ⟨rfl, is_stateless.state_elim so x.2⟩)) (by rw [is_stateless.state_elim so s]),
    end }

namespace is_stateless

lemma answer_query_eq_map_apply {i : spec.ι} (t : spec.domain i) [so.is_stateless] :
  so.answer_query i t = prod.fst <$> so i (t, so.default_state) := rfl

@[simp] lemma update_state_eq_const {s : S} {i : spec.ι} (t : spec.domain i) (u : spec.range i)
  [so.is_stateless] : so.update_state s i t u = so.default_state := rfl

section apply

variables [hso : so.is_stateless] {i : spec.ι} (s : S) (t : spec.domain i)
include hso

@[pairwise_dist_equiv] lemma apply_dist_equiv :
  so i (t, s) ≃ₚ (so.answer_query i t ×ₘ return so.default_state) :=
by rw_dist_equiv [is_tracking.apply_dist_equiv, map_return_dist_equiv]

@[simp] lemma support_apply : (so i (t, s)).support =
  prod.fst ⁻¹' (so.answer_query i t).support :=
trans (is_tracking.support_apply so t s) (by simp [set.ext_iff, prod.eq_iff_fst_eq_snd_eq])

@[simp] lemma fin_support_apply : (so i (t, s)).fin_support =
  (so.answer_query i t).fin_support.preimage prod.fst
    (λ x hx y hy h, (prod.eq_iff_fst_eq_snd_eq.2 ⟨h, state_elim' so x.2 y.2⟩)) :=
by rw [fin_support_eq_iff_support_eq_coe, support_apply, finset.coe_preimage,
  coe_fin_support_eq_support]

@[simp] lemma eval_dist_apply : ⁅so i (t, s)⁆ =
  (⁅so.answer_query i t⁆ ×ₘ (pmf.pure so.default_state)) :=
begin
  refine trans (is_tracking.eval_dist_apply so t s) _,
  simp only [mprod.def, pmf.map, update_state_eq_const],
  refine congr_arg (λ x, _ >>= x) (funext (λ x, trans (by refl) (pmf.pure_bind _ _).symm)),
end

@[simp] lemma prob_output_apply (z : spec.range i × S) :
  ⁅= z | so i (t, s)⁆ = ⁅= z.1 | so.answer_query i t⁆ :=
trans (is_tracking.prob_output_apply so t s z) (prob_event_eq_prob_output _ _
  (prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, is_stateless.state_elim' so _ _⟩) (λ y hy hy',
    (hy ((prod.eq_iff_fst_eq_snd_eq.1 hy').1)).elim))

@[simp] lemma prob_event_apply (e : set (spec.range i × S)) : ⁅e | so i (t, s)⁆ =
  ⁅prod.fst '' e | so.answer_query i t⁆ :=
begin
  haveI : unique S := is_stateless.state_unique so,
  refine trans (is_tracking.prob_event_apply so t s e) (prob_event_eq_of_mem_iff _ _ _ (λ u, _ )),
  simp [unique.exists_iff, state_elim' so default so.default_state],
end

end apply

section default_simulate

variables [hso : so.is_stateless] (oa : oracle_comp spec α) (s s' : S)
include hso

lemma simulate_eq_default_simulate : simulate so oa s = default_simulate so oa :=
@simulate_eq_default_simulate α spec spec' S so oa s hso.state_subsingleton

lemma simulate'_eq_default_simulate' : simulate' so oa s = default_simulate' so oa :=
@simulate'_eq_default_simulate' α spec spec' S so oa s hso.state_subsingleton

@[pairwise_dist_equiv] lemma simulate_dist_equiv_simulate_diff_state :
  simulate so oa s ≃ₚ simulate so oa s' :=
by rw [simulate_eq_default_simulate, simulate_eq_default_simulate]

@[pairwise_dist_equiv] lemma simulate'_dist_equiv_simulate'_diff_state :
  simulate' so oa s ≃ₚ simulate' so oa s' :=
by rw [simulate'_eq_default_simulate', simulate'_eq_default_simulate']

lemma simulate_dist_equiv_default_simulate' : simulate so oa s ≃ₚ
  (default_simulate' so oa ×ₘ return so.default_state) :=
begin
  simp_rw_dist_equiv [map_return_dist_equiv', map_bind_dist_equiv, map_return_dist_equiv'],
  refine trans (dist_equiv_of_eq (simulate_eq_default_simulate so oa s)) _,
  refine symm (bind_dist_equiv_left _ _ (λ z hz, _)),
  simp only [prod.eq_iff_fst_eq_snd_eq, return_dist_equiv_return_iff', eq_self_iff_true,
    default_state_eq_iff_true, and_self],
end

end default_simulate

section simulate_idem

variables [hso : so.is_stateless] {i : spec.ι} (t : spec.domain i)
  (oa : oracle_comp spec α) (s : S)
include hso

/-- If `so` is a stateless oracle, and its `answer_query` function is equivalent to `query`,
then simulation with `so` is equivalent to the original computation.  -/
lemma simulate_dist_equiv_self
  (h : ∀ i t, so.answer_query i t ≃ₚ query i t) :
  simulate so oa s ≃ₚ (oa ×ₘ return so.default_state) :=
begin
  rw_dist_equiv [simulate_dist_equiv_default_simulate'],
  refine mprod_dist_equiv_mprod _ (return_dist_equiv_return _ _ _),
  exact is_tracking.simulate'_dist_equiv_self so oa so.default_state h,
end

lemma support_simulate_eq_support
  (h : ∀ i t, (so.answer_query i t).support = set.univ) :
  (simulate so oa s).support = oa.support ×ˢ {so.default_state} :=
trans (simulate_dist_equiv_default_simulate' so oa s).support_eq
  (by rw [support_mprod, support_return, is_tracking.support_simulate'_eq_support so oa _ h])

lemma fin_support_simulate_eq_fin_support
  (h : ∀ i t, (so.answer_query i t).fin_support = finset.univ) :
  (simulate so oa s).fin_support = oa.fin_support ×ˢ {so.default_state} :=
begin
  rw [fin_support_eq_iff_support_eq_coe, finset.coe_product, finset.coe_singleton,
    coe_fin_support_eq_support, support_simulate_eq_support so oa _ (λ i t, _)],
  simpa only [fin_support_eq_iff_support_eq_coe, finset.coe_univ] using h i t
end

lemma eval_dist_simulate_eq_eval_dist
  (h : ∀ i t, ⁅so.answer_query i t⁆ = pmf.uniform_of_fintype (spec.range i)) :
  ⁅simulate so oa s⁆ = ⁅oa ×ₘ return so.default_state⁆ :=
begin
  rw_dist_equiv [simulate_dist_equiv_self so oa s],
  simp only [dist_equiv.def, h, eval_dist_query, eq_self_iff_true, forall_2_true_iff]
end

lemma prob_output_simulate_eq_prob_output
  (h : ∀ i t u, ⁅= u | so.answer_query i t⁆ = (fintype.card (spec.range i))⁻¹)
  (z : α × S) : ⁅= z | simulate so oa s⁆ = ⁅= z.1 | oa⁆ :=
begin
  haveI : subsingleton S := hso.state_subsingleton,
  refine trans ((simulate_dist_equiv_self so oa s (λ i t, dist_equiv.ext
    (λ u, (h i t u).trans (prob_output_query_eq_inv i t u).symm))).prob_output_eq z) _,
  rw [prob_output_mprod, prob_output_of_subsingleton _ z.2, mul_one]
end

lemma prob_event_simulate_eq_prob_output
  (h : ∀ i t u, ⁅= u | so.answer_query i t⁆ = (fintype.card (spec.range i))⁻¹)
  (e : set (α × S)) : ⁅e | simulate so oa s⁆ = ⁅prod.fst '' e | oa⁆ :=
begin
  haveI : unique S := state_unique so,
  refine trans ((simulate_dist_equiv_self so oa s (λ i t, dist_equiv.ext
    (λ u, (h i t u).trans (prob_output_query_eq_inv i t u).symm))).prob_event_eq e) _,
  have : e = (prod.fst '' e) ×ˢ {so.default_state},
  { refine set.ext (λ z, z.rec_on (λ x y, _)),
    simp [state_elim' so y default, unique.exists_iff] },
  rw [this, prob_event_mprod_eq_mul, set.fst_image_prod _ (set.singleton_nonempty _),
    prob_event_singleton_eq_prob_output, prob_output_return_self, mul_one]
end

end simulate_idem

section simulate_eq_simulate


variables [hso : so.is_stateless] [hso' : so'.is_stateless]
  {i : spec.ι} (t : spec.domain i) (oa : oracle_comp spec α) (s : S) (s' : S')
include hso hso'

lemma simulate_dist_equiv_simulate
  (h : ∀ i t,  so.answer_query i t ≃ₚ so'.answer_query i t) :
  simulate so oa s ≃ₚ simulate so' oa s :=
begin
  sorry,
end


end simulate_eq_simulate

end is_stateless

end sim_oracle


/-- Simulate a computation without making use of the internal state.
  We use the `unit` type as the state in this case, so all possible states are equal.
  Implemented as a `tracking_oracle` where the state isn't actually tracking anything -/
def stateless_oracle (query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)) :
  sim_oracle spec spec' unit :=
{ default_state := (),
  o := λ i ⟨t, s⟩, query_f i t ×ₘ return () }
-- ⟪query_f | λ _ _ _ _, (), ()⟫

notation `⟪` query_f `⟫` := stateless_oracle query_f

variables (query_f : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))

instance stateless_oracle.is_stateless : ⟪query_f⟫.is_stateless :=
{ state_subsingleton := punit.subsingleton }

namespace stateless_oracle

open sim_oracle

variables {i : spec.ι} (t : spec.domain i) (s : unit) (u : spec.range i)

lemma apply_eq : ⟪query_f⟫ i (t, s) = (query_f i t ×ₘ return ()) := rfl

lemma answer_query_eq : ⟪query_f⟫.answer_query i t = prod.fst <$> (query_f i t ×ₘ return ()) := rfl

lemma update_state_eq : ⟪query_f⟫.update_state s i t u = () := rfl

lemma answer_query_dist_equiv : ⟪query_f⟫.answer_query i t ≃ₚ query_f i t :=
by pairwise_dist_equiv

@[simp] lemma support_answer_query :
  (⟪query_f⟫.answer_query i t).support = (query_f i t).support := by pairwise_dist_equiv

@[simp] lemma fin_support_answer_query :
  (⟪query_f⟫.answer_query i t).fin_support = (query_f i t).fin_support := by pairwise_dist_equiv

@[simp] lemma eval_dist_answer_query :
  ⁅⟪query_f⟫.answer_query i t⁆ = ⁅query_f i t⁆ := by pairwise_dist_equiv

@[simp] lemma prob_output_answer_query (u : spec.range i) :
  ⁅= u | ⟪query_f⟫.answer_query i t⁆ = ⁅= u | query_f i t⁆ := by pairwise_dist_equiv

@[simp] lemma prob_event_answer_query (e : set (spec.range i)) :
  ⁅e | ⟪query_f⟫.answer_query i t⁆ = ⁅e | query_f i t⁆ := by pairwise_dist_equiv

end stateless_oracle

-- More lemmas we can prove about `tracking_oracle` with the definition of the `stateless_oracle`
-- namespace tracking_oracle

-- -- variables (oa : oracle_comp spec α)
-- --   (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
-- --   (o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i))
-- --   (i : spec.ι) (t : spec.domain i) (s s' : unit) (u : spec.range i)
-- --   (x : spec.domain i × unit) (y : spec.range i × unit)


-- variables
--   (update_state update_state': Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
--   (default_state default_state' s s' : S) (oa : oracle_comp spec α)

-- section support

-- /-- The first output with a tracking oracle is independent of any of the tracking state -/
-- lemma support_simulate'_eq_support_simulate'_stateless_oracle :
--   (simulate' ⟪o | update_state, default_state⟫ oa s).support = (simulate' ⟪o⟫ oa ()).support :=
-- begin
--   sorry
--   -- unfold stateless_oracle,
--   -- refine support_simulate'_eq_of_oracle_eq o update_state (λ _ _ _ _, ()) default_state _ oa s _
-- end

-- end support

-- section distribution_semantics

-- /-- The first output of a tracking oracle is equivalent to using just the stateless oracle -/
-- lemma simulate'_equiv_stateless_oracle :
--   simulate' ⟪o | update_state, default_state⟫ oa s ≃ₚ simulate' ⟪o⟫ oa () :=
-- begin
--   sorry
--   -- induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
--   -- { simp },
--   -- { let so := ⟪o|update_state, default_state⟫,
--   --   calc simulate' so (oa >>= ob) s
--   --     ≃ₚ (simulate so oa s) >>= (λ x, simulate' so (ob x.1) x.2) :
--               --simulate'_bind_equiv so oa ob s
--   --     ... ≃ₚ (simulate so oa s) >>= (λ x, simulate' ⟪o⟫ (ob x.1) ()) :
--   --       bind_equiv_of_equiv_second _ (λ a, (hob a.1 a.2))
--   --     ... ≃ₚ (simulate' so oa s) >>= (λ x, simulate' ⟪o⟫ (ob x) ()) : by erw [bind_map_equiv]
--   --     ... ≃ₚ (simulate' ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x) ()) :
--   --       bind_equiv_of_equiv_first _ (hoa _)
--   --     ... ≃ₚ (simulate ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x.1) ()) : by erw [bind_map_equiv]
--   --     ... ≃ₚ (simulate ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x.1) x.2) :
--   --       by { congr, ext x, rw [punit_eq () x.2] }
--   --     ... ≃ₚ simulate' ⟪o⟫ (oa >>= ob) () : by rw [simulate'_bind_equiv] },
--   -- { simp_rw [simulate'_query_equiv, apply_eq, stateless_oracle.apply_eq, map_bind_equiv],
--   --   refine bind_equiv_of_equiv_second (o i t) _,
--   --   simp only [map_pure_equiv, eq_self_iff_true, forall_const] }
-- end

-- /-- The first ouptput of a tracking oracle is indepenedent of the actual tracking functions
-- TODO: `so.answer_query i t ≃ₚ so'.answer_query i t` -/
-- lemma simulate'_equiv_of_equiv (h : ∀ i t, o i t ≃ₚ o' i t) :
--   simulate' ⟪o | update_state, default_state⟫ oa s ≃ₚ
--     simulate' ⟪o' | update_state', default_state'⟫ oa s' :=
-- calc simulate' ⟪o | update_state, default_state⟫ oa s
--   ≃ₚ simulate' ⟪o⟫ oa () : simulate'_equiv_stateless_oracle o update_state default_state s oa
--   ... ≃ₚ simulate' ⟪o'⟫ oa () :
--     sorry --stateless_oracle.eval_dist_simulate'_eq_eval_dist_simulate' _ _ _ _ _ h
--   ... ≃ₚ simulate' ⟪o' | update_state', default_state'⟫ oa s' :
--     symm (simulate'_equiv_stateless_oracle o' update_state' default_state' _ _)

-- end distribution_semantics

-- end tracking_oracle