/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.simulation_semantics.simulate.query
import computational_monads.distribution_semantics.tactics.pairwise_dist_equiv

/-!
# Distributions of Simulations

This file contains more complicated lemmas for `eval_dist` applied to `simulate` and `simulate'`.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale nnreal ennreal

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa oa' : oracle_comp spec α)
  (ob ob' : α → oracle_comp spec β) (s : S) (f : α → β)

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind` -/
lemma eval_dist_simulate_eq_induction {pr : Π (α : Type), oracle_comp spec α → S → (pmf (α × S))}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, pr α (return a) s = pmf.pure (a, s))
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    pr β (oa >>= ob) s = (pr α oa s).bind (λ x, pr β (ob x.1) x.2))
  (h_query : ∀ i t s, pr (spec.range i) (query i t) s = ⁅so i (t, s)⁆) :
  ⁅simulate so oa s⁆ = pr α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a' α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate_return, eval_dist_return] },
  { simp only [h_bind, hoa, hob, simulate_bind, eval_dist_bind] },
  { simp only [h_query, simulate_query] }
end

/-- Lemma for inductively proving that the distribution associated to a simulation
is a specific function. Gives more explicit criteria than induction on the computation.
In particular this automatically splits the cases for `return` and the `prod` in the `bind` sum. -/
lemma prob_output_simulate_eq_induction
  {pr : Π (α : Type), oracle_comp spec α → S → α × S → ℝ≥0∞}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S) (a : α) (s' : S)
  (h_ret : ∀ α a s, pr α (return a) s (a, s) = 1)
  (h_ret' : ∀ α a a' s s', a ≠ a' ∨ s ≠ s' → pr α (return a) s (a', s') = 0)
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s b s',
    pr β (oa >>= ob) s (b, s') = ∑' (a : α) (t : S), (pr α oa s (a, t)) * (pr β (ob a) t (b, s')))
  (h_query : ∀ i t s u s', pr (spec.range i) (query i t) s (u, s') = ⁅so i (t, s)⁆ (u, s')) :
  ⁅= (a, s') | simulate so oa s⁆ = pr α oa s (a, s') :=
begin
  induction oa using oracle_comp.induction_on with α a' α β oa ob hoa hob i t generalizing s s',
  {
    rw [prob_output_simulate_return_eq_indicator, set.indicator],
    -- rw [eval_dist_simulate_return, pmf.pure_apply],
    split_ifs with has,
    { simp only [set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq] at has,
      refine has.1 ▸ has.2.symm ▸ (h_ret α a s).symm, },
    { simp only [set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq, not_and_distrib] at has,
      cases has with ha hs,
      { exact (h_ret' α a' a s s' $ or.inl $ ne.symm ha).symm },
      { exact (h_ret' α a' a s s' $ or.inr $ ne.symm hs).symm } }

  },
  { simp only [prob_output_simulate_bind_eq_tsum_tsum, h_bind, hoa, hob] },
  { rw [prob_output_simulate_query, h_query, prob_output.def] },
end

/-- If the main output of oracle queries is uniformly distributed (ignoring the oracle state),
then the output distribution under `simulate'` is exactly the original distribution,
since we define `eval_dist` to be uniform on oracle calls. -/
theorem eval_dist_simulate'_eq_eval_dist
  (h : ∀ i t s, ⁅so i (t, s)⁆.map prod.fst = pmf.uniform_of_fintype (spec.range i)) :
  ⁅simulate' so oa s⁆ = ⁅oa⁆ :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [simulate'_return, eval_dist_map_return, eval_dist_return] },
  { refine eval_dist.prob_output_ext _ _ (λ x, _),
    rw [prob_output_bind_eq_tsum_indicator, prob_output_simulate'_bind_eq_tsum_tsum],
    refine tsum_congr (λ a, _),
    sorry,
    -- rw [← hoa s, prob_output_simulate', ← ennreal.tsum_mul_right],
    -- refine tsum_congr (λ t, _),
    -- rw ← hob
    },
  { simp only [h, simulate'_query, eval_dist_map, eval_dist_query] }
end

/-- Given two simulation oracles `so` and `so'`, if the output distribution of oracle queries
(ignoring the output state) is the same for any input and pair of initial oracle states,
then the output distribution of simulating a computation is the same for both. -/
theorem eval_dist_simulate'_eq_eval_dist_simulate'
  {so : sim_oracle spec spec' S} {so' : sim_oracle spec spec'' S'}
  (h : ∀ i t s s', ⁅so i (t, s)⁆.map prod.fst = ⁅so' i (t, s')⁆.map prod.fst)
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

end oracle_comp