/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.induction
import computational_monads.constructions.uniform_select

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

variables {so : sim_oracle spec spec' S} (oa : oracle_comp spec α) (s : S)

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
  { rw_dist_equiv [simulate'_query_dist_equiv, h i t s] }
end

/-- If the distribution of the first output of `sim_oracle` is uniform
(although the distribution of the state output may be arbitrary), then the
first result of simulation by that oracle has the same distribution as the original computation. -/
lemma eval_dist_simulate'_eq_eval_dist
  (h : ∀ i t s, ⁅so i (t, s)⁆.map fst = pmf.uniform_of_fintype (spec.range i)) :
  ⁅simulate' so oa s⁆ = ⁅oa⁆ :=
begin
  refine dist_equiv.eval_dist_eq (simulate'_dist_equiv_self oa s (λ i t s, _)),
  simp [dist_equiv.def, h i t s],
end

/-- If the probability of getting a result as the first output of a `sim_oracle` is uniform
(although the distribution of the state output may be arbitrary),
then the first result of simulation by that oracle is the same as the original computation. -/
lemma prob_output_simulate'_eq_prob_output
  (h : ∀ i t s u, ⁅= u | fst <$> so i (t, s)⁆ = (fintype.card (spec.range i))⁻¹)
  (x : α) : ⁅= x | simulate' so oa s⁆ = ⁅= x | oa⁆ :=
begin
  refine dist_equiv.prob_output_eq (simulate'_dist_equiv_self oa s (λ i t s, _)) x,
  simp [dist_equiv.ext_iff, h i t s, prob_output_query_eq_inv],
end

/-- If the probability of getting a result as the first output of a `sim_oracle` is uniform
(although the distribution of the state output may be arbitrary),
then the chance of an event holding on the first result of simulating by that oracle
is the same as the chance of it holding on the original computation. -/
lemma prob_event_simulate'_eq_prob_event
  (h : ∀ i t s u, ⁅= u | fst <$> so i (t, s)⁆ = (fintype.card (spec.range i))⁻¹)
  (e : set α) : ⁅e | simulate' so oa s⁆ = ⁅e | oa⁆ :=
prob_event_eq_of_prob_output_eq (λ x _, prob_output_simulate'_eq_prob_output oa s h x)

/-- If the first output of a `sim_oracle` can take on an arbitrary value,
then the first output of simulating with that oracle can take the same values as the original. -/
lemma support_simulate'_eq_support
  (h : ∀ i t s, fst '' (so i (t, s)).support = set.univ) :
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

/-- Version of `support_simulate'_eq_support` for `simulate'`. -/
lemma fin_support_simulate'_eq_fin_support [decidable_eq α] [decidable_eq S]
  (h : ∀ i t s, (so i (t, s)).fin_support.image fst = finset.univ) :
  (simulate' so oa s).fin_support = oa.fin_support :=
begin
  rw [fin_support_eq_fin_support_iff_support_eq_support],
  refine support_simulate'_eq_support oa s (λ i t s, _),
  simpa only [finset.coe_image, coe_fin_support, finset.coe_univ] using
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
  { simp_rw_dist_equiv [simulate'_query_dist_equiv],
    exact h i t s s' }
end

/-- If the distributions of the first result of two oracles are the same for any input,
then the first results of simulation by those oracles have the same distribution. -/
lemma eval_dist_simulate'_eq_eval_dist_simulate'
  (h : ∀ i t s s', ⁅so i (t, s)⁆.map fst = ⁅so' i (t, s')⁆.map fst) :
  ⁅simulate' so oa s⁆ = ⁅simulate' so' oa s'⁆ :=
begin
  refine (simulate'_dist_equiv_simulate' oa s s' (λ i t s s', _)).eval_dist_eq,
  simp [dist_equiv.def, h i t s s'],
end

/-- If the probability of the first output of two oracles match for any output,
then the probability of getting the same first output of simulation with either oracle
are exactly the same. -/
lemma prob_output_simulate'_eq_prob_output_simulate'
  (h : ∀ i t s s' u, ⁅= u | fst <$> so i (t, s)⁆ = ⁅= u | fst <$> so' i (t, s')⁆)
  (x : α) : ⁅= x | simulate' so oa s⁆ = ⁅= x | simulate' so' oa s'⁆ :=
begin
  refine (simulate'_dist_equiv_simulate' oa s s' (λ i t s s', _)).prob_output_eq x,
  simp only [dist_equiv.ext_iff, h i t s s', eq_self_iff_true, forall_const],
end

/-- If the probability of the first output of two oracles match for any output,
then the probability of an event on the first output of simulation with either oracle
is exactly the same for any initial states. -/
lemma prob_event_simulate'_eq_prob_event_simulate'
  (h : ∀ i t s s' u, ⁅= u | fst <$> so i (t, s)⁆ = ⁅= u | fst <$> so' i (t, s')⁆)
  (e : set α) : ⁅e | simulate' so oa s⁆ = ⁅e | simulate' so' oa s'⁆ :=
begin
  refine (simulate'_dist_equiv_simulate' oa s s' (λ i t s s', _)).prob_event_eq e,
  simp only [dist_equiv.ext_iff, h i t s s', eq_self_iff_true, forall_const],
end

/-- If the possible outputs of two oracles are the same for any inputs regardless of their
internal states, then the `support` of `simulate'` with either oracle is the same.
Intuitively the simulations *could* take the same branch at each oracle query, and while the
probabilities of divergence may vary, this doesn't affect the set of possible results. -/
lemma support_simulate'_eq_support_simulate'
  (h : ∀ i t s s', prod.fst '' (so i (t, s)).support = prod.fst '' (so' i (t, s')).support) :
  (simulate' so oa s).support = (simulate' so' oa s').support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s s',
  { simp only [simulate'_return, support_map, support_return, set.image_singleton] },
  { ext x,
    simp_rw [support_simulate'_bind, set.mem_Union],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨⟨a, t⟩, hoa', hob'⟩ := h,
      have : ∃ u, (a, u) ∈ (simulate so oa s).support := ⟨t, hoa'⟩,
      rw [← mem_support_simulate'_iff_exists_state, hoa s s',
        mem_support_simulate'_iff_exists_state] at this,
      obtain ⟨t', ht'⟩ := this,
      exact ⟨(a, t'), ht', hob a t t' ▸ hob'⟩ },
    { obtain ⟨⟨a, t⟩, hoa', hob'⟩ := h,
      have : ∃ u, (a, u) ∈ (simulate so' oa s').support := ⟨t, hoa'⟩,
      rw [← mem_support_simulate'_iff_exists_state, ← hoa s s',
        mem_support_simulate'_iff_exists_state] at this,
      obtain ⟨t', ht'⟩ := this,
      exact ⟨(a, t'), ht', (hob a t' t).symm ▸ hob'⟩ } },
  { simpa only [support_simulate'_query] using h i t s s' }
end

lemma fin_support_simulate'_eq_fin_support_simulate'
  [decidable_eq α] [decidable_eq S] [decidable_eq S']
  (h : ∀ i t s s', (so i (t, s)).fin_support.image fst = (so' i (t, s')).fin_support.image fst) :
  (simulate' so oa s).fin_support = (simulate' so' oa s').fin_support :=
fin_support_eq_fin_support_of_support_eq_support _ _ (support_simulate'_eq_support_simulate' oa s
  s' (λ i t s s', by simpa only [finset.coe_image, coe_fin_support]
  using congr_arg (λ s, (↑s : set (spec.range i))) (h i t s s')))

end simulate'_eq_simulate'

section simulate_eq_simulate

variables {so : sim_oracle spec spec' S} {so' : sim_oracle spec spec'' S}
  (oa : oracle_comp spec α) (s : S) (s' : S)

/-- If the possible outputs (including state) of applying to different `sim_oracle`s is the same
(although the probability may differ between the two), then simulation with either oracle will give
the same support for any computation. -/
lemma support_simulate_eq_support_simulate
  (h : ∀ i t s s', (so i (t, s)).support = (so' i (t, s')).support) :
  (simulate so oa s).support = (simulate so' oa s).support :=
begin
  refine support_simulate_eq_induction so oa s _ (λ _ _ _ _ _, _) (λ _ _ _, _),
  { simp only [simulate_return, support_return, eq_self_iff_true, forall_3_true_iff] },
  { simp only [simulate_bind, support_bind, eq_self_iff_true] },
  { rw [simulate_query, h]  }
end

/-- Version of `support_simulate_eq_support_simulate` for `fin_support`. -/
lemma fin_support_simulate_eq_fin_support_simulate
  [decidable_eq α] [decidable_eq S] [decidable_eq S']
  (h : ∀ i t s s', (so i (t, s)).fin_support = (so' i (t, s')).fin_support) :
  (simulate so oa s).fin_support = (simulate so' oa s).fin_support :=
fin_support_eq_fin_support_of_support_eq_support _ _ (support_simulate_eq_support_simulate
  oa s (λ i t s s', (fin_support_eq_fin_support_iff_support_eq_support _ _).1 (h i t s s')))

end simulate_eq_simulate

end oracle_comp