/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.simulation_semantics.simulate.query
import computational_monads.distribution_semantics.tactics.pairwise_dist_equiv

/-!
# Simulation with Oracles That Only Modify State

This file contains lemmas for relating the distribution semantics of `simulate'` to that of
the original computation, given relations between applications of the oracles.
This is especially useful for oracles with `is_tracking` instances, as they split the state
and main portion of the oracle into distinct functions.
-/

namespace oracle_comp

open oracle_spec prod

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

section simulate'_eq_self

variables (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)

/-- If taking the first result of applying a simulation oracle is equivalent to just querying the
oracle, then the first result of simulating an arbitrary computation with an arbitrary initial
state is equivalent to the original computation. -/
lemma simulate'_dist_equiv_self (h : ∀ i t s, fst <$> so i (t, s) ≃ₚ query i t) :
  simulate' so oa s ≃ₚ oa :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { rw_dist_equiv [simulate'_return_dist_equiv] },
  { simp [dist_equiv.ext_iff] at hoa hob,
    refine dist_equiv.ext (λ y, _),
    simp_rw [prob_output_simulate'_bind_eq_tsum_tsum, hob, ennreal.tsum_mul_right,
      ← prob_output_simulate', hoa, prob_output_bind_eq_tsum] },
  { exact h i t s }
end

lemma eval_dist_simulate'_eq_eval_dist
  (h : ∀ i t s, ⁅so i (t, s)⁆.map fst = pmf.uniform_of_fintype (spec.range i)) :
  ⁅simulate' so oa s⁆ = ⁅oa⁆ :=
begin
  refine dist_equiv.eval_dist_eq (simulate'_dist_equiv_self so oa s (λ i t s, _)),
  simp [dist_equiv.def, h i t s],
end

lemma prob_output_simulate'_eq_prob_output
  (h : ∀ i t s u, ⁅= u | fst <$> so i (t, s)⁆ = (fintype.card (spec.range i))⁻¹)
  (x : α) : ⁅= x | simulate' so oa s⁆ = ⁅= x | oa⁆ :=
begin
  refine dist_equiv.prob_output_eq (simulate'_dist_equiv_self so oa s (λ i t s, _)) x,
  simp [dist_equiv.ext_iff, h i t s, prob_output_query_eq_inv],
end

lemma prob_event_simulate'_eq_prob_event
  (h : ∀ i t s u, ⁅= u | fst <$> so i (t, s)⁆ = (fintype.card (spec.range i))⁻¹)
  (e : set α) : ⁅e | simulate' so oa s⁆ = ⁅e | oa⁆ :=
prob_event_eq_of_prob_output_eq (λ x _, prob_output_simulate'_eq_prob_output so oa s h x)

lemma support_simulate'_eq_support (h : ∀ i t s, fst '' (so i (t, s)).support = set.univ) :
  (simulate' so oa s).support = oa.support :=
begin
  refine set.eq_of_subset_of_subset (support_simulate'_subset_support so oa s) (λ x hx, _),
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simpa only [simulate'_return, support_map, support_return, set.image_singleton] using hx },
  { simp only [support_simulate'_bind, support_bind, set.mem_Union] at hx ⊢,
    obtain ⟨a, ha, hx⟩ := hx,
    specialize hoa a ha s,
    rw [support_simulate', set.mem_image] at hoa,
    obtain ⟨⟨a', s'⟩, ha', ha''⟩ := hoa,
    exact ⟨(a', s'), ha', hob a' x (let this : a = a' := ha''.symm in this ▸ hx) s'⟩ },
  { simp only [support_simulate'_query, h i t s] }
end

lemma fin_support_simulate'_eq_fin_support
  (h : ∀ i t s, (so i (t, s)).fin_support.image fst = finset.univ) :
  (simulate' so oa s).fin_support = oa.fin_support :=
begin
  rw [fin_support_eq_fin_support_iff_support_eq_support],
  refine support_simulate'_eq_support so oa s (λ i t s, _),
  simpa only [finset.coe_image, coe_fin_support_eq_support, finset.coe_univ] using
    (congr_arg (λ s, ↑s : finset (spec.range i) → set (spec.range i)) (h i t s)),
end

end simulate'_eq_self

section simulate'_eq_simulate'

variables {so : sim_oracle spec spec' S} {so' : sim_oracle spec spec'' S'}
  (oa : oracle_comp spec α) (s : S) (s' : S')

/-- If two simulation oracles return the same result on a query regardless of their current state,
then (ignoring the final state) simulation with either oracle gives equivalent computations. -/
lemma simulate'_dist_equiv_simulate'
  (h : ∀ i t s s', fst <$> so i (t, s) ≃ₚ fst <$> so' i (t, s')) :
  simulate' so oa s ≃ₚ simulate' so' oa s' :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s s',
  { push_map_dist_equiv },
  { simp only [dist_equiv.ext_iff] at hoa hob,
    refine dist_equiv.ext (λ z, _),
    simp_rw [prob_output_simulate'_bind_eq_tsum_tsum, hob _ _ s', ennreal.tsum_mul_right,
      ← prob_output_simulate', hoa s s', prob_output_simulate' _ oa, ← ennreal.tsum_mul_right],
    exact tsum_congr (λ x, tsum_congr (λ s₁, congr_arg (λ r, _ * r)
      (trans (hob _ s _ z).symm (hob _ _ _ z)))) },
  { exact h i t s s' }
end

lemma eval_dist_simulate'_eq_eval_dist_simulate'
  {so : sim_oracle spec spec' S} {so' : sim_oracle spec spec'' S'}
  (h : ∀ i t s s', ⁅so i (t, s)⁆.map fst = ⁅so' i (t, s')⁆.map fst)
  (oa : oracle_comp spec α) (s : S) (s' : S') :
  ⁅simulate' so oa s⁆ = ⁅simulate' so' oa s'⁆ :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s s',
  { simp only [simulate'_return, eval_dist_map_return] },
  { refine eval_dist.prob_output_ext _ _ (λ b, _),
    simp only [prob_output_simulate'_bind_eq_tsum_tsum],
    refine tsum_congr (λ a, _),
    sorry,
    -- calc ∑' (t : S), ⁅= (a, t) | simulate so oa s⁆ * ⁅= b | simulate' so (ob a) t⁆
    --   = ∑' (t : S), ⁅= (a, t) | simulate so oa s⁆ * ⁅= b | simulate' so' (ob a) s'⁆ :
    --     tsum_congr (λ t, congr_arg (λ x, _ * x) $ by rw hob a t s')
    --   ... = (∑' (t' : S'), ⁅simulate so' oa s'⁆ (a, t')) * ⁅simulate' so' (ob a) s'⁆ b :
    --     by simp_rw [ennreal.tsum_mul_right, ← prob_output_simulate', hoa s s']
    --   ... = ∑' (t' : S'), ⁅simulate so' oa s'⁆ (a, t') * ⁅simulate' so (ob a) s⁆ b :
    --     by rw [ennreal.tsum_mul_right, hob]
    --   ... = ∑' (t' : S'), ⁅simulate so' oa s'⁆ (a, t') * ⁅simulate' so' (ob a) t'⁆ b :
    --     tsum_congr (λ t, congr_arg (λ x, _ * x) $ by rw hob)
        },
  { simpa only [simulate'_query, eval_dist_map] using h i t s s' },
end

end simulate'_eq_simulate'

end oracle_comp