/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.eval_dist

/-!
# Probability of Events

This file defines the probability of some event holding after running a computation.
The definition is in terms of the `measure` associated to the `pmf` given by `eval_dist`.

This definition is equivalent to one in terms of summations, in particular an infinite `tsum`.
If the support is decidable (or the event is a `finset`),
we can instead give an expression in terms of `finset.sum`.
-/

namespace distribution_semantics

open oracle_comp oracle_spec
open_locale big_operators nnreal ennreal

variables {α β γ ι : Type} {spec spec' : oracle_spec}  [finite_range spec] [finite_range spec']
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (a a' : α)
  (e e' : set α) (e'' : set β)

/-- Probability of a predicate holding after running a particular experiment.
Defined in terms of the outer measure associated to the corresponding `pmf`.
The initial definition uses a `measure` to access more general lemmas,
but is equal to the `outer_measure` (see `prob_event_eq_to_outer_measure_apply`). -/
noncomputable def prob_event (oa : oracle_comp spec α) (event : set α) : ℝ≥0∞ :=
⦃oa⦄.to_outer_measure event

notation `⦃` event `|` oa `⦄` := prob_event oa event

lemma prob_event.def : ⦃e | oa⦄ = ⦃oa⦄.to_outer_measure e := rfl

lemma prob_event_eq_to_measure_apply : ⦃e | oa⦄ = (@pmf.to_measure α ⊤ ⦃oa⦄ e) :=
(@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ ⦃oa⦄ e
  measurable_space.measurable_set_top).symm

lemma prob_event_le_one : ⦃e | oa⦄ ≤ 1 :=
(⦃oa⦄.to_outer_measure.mono (set.subset_univ e)).trans
  (le_of_eq $ (⦃oa⦄.to_outer_measure_apply_eq_one_iff _).2 (set.subset_univ ⦃oa⦄.support))

/-- Probability of an event in terms of non-decidable `set.indicator` sum -/
lemma prob_event_eq_tsum_indicator : ⦃e | oa⦄ = ∑' x, e.indicator ⦃oa⦄ x :=
pmf.to_outer_measure_apply ⦃oa⦄ e

/-- Probability of an event in terms of a decidable `ite` sum-/
lemma prob_event_eq_tsum_ite [decidable_pred (∈ e)] :
  ⦃e | oa⦄ = ∑' x, if x ∈ e then ⦃oa⦄ x else 0 :=
(prob_event_eq_tsum_indicator oa e).trans (tsum_congr $ λ x, by {unfold set.indicator, congr})

lemma prob_event_finset_eq_sum (e : finset α) :
  ⦃↑e | oa⦄ = ∑ x in e, ⦃oa⦄ x :=
by rw [prob_event_eq_tsum_indicator, finset.sum_eq_tsum_indicator]

lemma prob_event_le_prob_event_of_subset (oa : oracle_comp spec α) {e e' : set α}
  (h : (e ∩ oa.support) ⊆ e') : ⦃e | oa⦄ ≤ ⦃e' | oa⦄ :=
calc ⦃e | oa⦄
  = ∑' x, e.indicator ⦃oa⦄ x : prob_event_eq_tsum_indicator oa e
  ... = ∑' x, (e ∩ oa.support).indicator ⦃oa⦄ x : begin
    refine tsum_congr (λ x, _),
    by_cases hx : x ∈ e,
    { by_cases hx' : x ∈ (e ∩ oa.support),
      { rw [(set.indicator_apply_eq_self).2 (λ h', (h' hx).elim),
          (set.indicator_apply_eq_self).2 (λ h', (h' hx').elim)] },
      { have : ⦃oa⦄ x = 0 := (eval_dist_eq_zero_of_not_mem_support $ λ h', hx' ⟨hx, h'⟩),
        simp only [set.indicator, hx, hx', if_true, if_false, this] } },
    { have hx' : x ∉ (e ∩ oa.support) := λ h', hx h'.1,
      rw [set.indicator_apply_eq_zero.2 (λ h', (hx h').elim),
        set.indicator_apply_eq_zero.2 (λ h', (hx' h').elim)] }
  end
  ... ≤ ∑' x, e'.indicator ⦃oa⦄ x : ennreal.tsum_le_tsum
    (λ x, set.indicator_le_indicator_of_subset h (λ _, zero_le') _)
  ... = ⦃e' | oa⦄ : (prob_event_eq_tsum_indicator oa e').symm

lemma prob_event_le_prob_event_of_subset' (oa : oracle_comp spec α) {e e' : set α}
  (h : e ⊆ e') : ⦃e | oa⦄ ≤ ⦃e' | oa⦄ :=
prob_event_le_prob_event_of_subset oa (trans (set.inter_subset_left _ _) h)

lemma prob_event_eq_of_eval_dist_eq {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : ⦃oa⦄ = ⦃oa'⦄) (e : set α) : ⦃e | oa⦄ = ⦃e | oa'⦄ :=
by simp_rw [prob_event, h]

-- -- TODO: only needed cause of random nnreal stuff
-- lemma prob_event_eq_mul_iff_to_outer_measure_apply_eq {oa : oracle_comp spec α} (e e' e'' : set α) :
--   ⦃e | oa⦄ = ⦃e' | oa⦄ * ⦃e'' | oa⦄ ↔
--     ⦃oa⦄.to_outer_measure e = (⦃oa⦄.to_outer_measure e') * (⦃oa⦄.to_outer_measure e'') :=
-- begin
--   -- simp_rw [prob_event_eq_to_nnreal_to_outer_measure_apply],
--   -- rw [← ennreal.to_nnreal_mul, ennreal.to_nnreal_eq_to_nnreal_iff'],
--   { exact pmf.to_outer_measure_apply_ne_top ⦃oa⦄ e },
--   { refine ennreal.mul_ne_top _ _; apply pmf.to_outer_measure_apply_ne_top }
-- end

-- lemma prob_event_eq_mul_iff_to_measure_apply_eq {oa : oracle_comp spec α} (e e' e'' : set α) :
--   ⦃e | oa⦄ = ⦃e' | oa⦄ * ⦃e'' | oa⦄ ↔
--     @pmf.to_measure α ⊤ ⦃oa⦄ e = (@pmf.to_measure α ⊤ ⦃oa⦄ e') * (@pmf.to_measure α ⊤ ⦃oa⦄ e'') :=
-- begin
--   rw [prob_event_eq_mul_iff_to_outer_measure_apply_eq,
--     pmf.to_measure_apply_eq_to_outer_measure_apply, pmf.to_measure_apply_eq_to_outer_measure_apply,
--       pmf.to_measure_apply_eq_to_outer_measure_apply];
--   exact measurable_space.measurable_set_top,
-- end

section return

lemma prob_event_return_eq_indicator :
  ⦃e | (return a : oracle_comp spec α)⦄ = e.indicator (λ _, 1) a :=
begin
  simp only [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply],
  split_ifs with h;
  simp only [h, set.indicator_of_mem, set.indicator_of_not_mem, not_false_iff],
end

@[simp]
lemma prob_event_return [decidable_pred (∈ e)] :
  ⦃e | (return a : oracle_comp spec α)⦄ = if a ∈ e then 1 else 0 :=
begin
  simp only [prob_event.def, eval_dist_return, pmf.to_outer_measure_pure_apply],
  congr, -- TODO: classical?
end

lemma prob_event_return_of_true (ha : a ∈ e) :
  ⦃ e | (return a : oracle_comp spec α) ⦄ = 1 :=
by simp only [ha, prob_event_return_eq_indicator, set.indicator_of_mem]

lemma prob_event_return_of_false (ha : a ∉ e) :
  ⦃ e | (return a : oracle_comp spec α) ⦄ = 0 :=
by simp only [ha, prob_event_return_eq_indicator, set.indicator_of_not_mem, not_false_iff]

end return

section bind

@[simp] lemma prob_event_bind : ⦃e'' | oa >>= ob⦄ = ∑' (a : α), ⦃oa⦄ a * ⦃e'' | ob a⦄ :=
by simp only [prob_event.def, eval_dist_bind, pmf.to_outer_measure_bind_apply]

@[simp] lemma prob_event_return_bind : ⦃e'' | return a >>= ob⦄ = ⦃e'' | ob a⦄ :=
prob_event_eq_of_eval_dist_eq (eval_dist_return_bind ob a) e''

@[simp] lemma prob_event_bind_return : ⦃e | oa >>= return⦄ = ⦃e | oa⦄ :=
prob_event_eq_of_eval_dist_eq (eval_dist_bind_return_id oa) e

end bind

section query

@[simp] lemma prob_event_query (i : spec.ι) (t : spec.domain i) (e : set $ spec.range i)
  [decidable_pred e] : ⦃ e | query i t ⦄ = fintype.card e / fintype.card (spec.range i) :=
begin
  rw [prob_event.def, eval_dist_query, pmf.to_outer_measure_uniform_of_fintype_apply],
  congr -- TODO: classical
end

end query

section map

@[simp] lemma prob_event_map (f : α → β) (e : set β) : ⦃e | f <$> oa⦄ = ⦃f ⁻¹' e | oa⦄ :=
by simp only [prob_event.def, eval_dist_map, pmf.to_outer_measure_map_apply]

end map

section support

/-- Given a `finset` containing the `support` of some `oracle_comp`,
  it suffices to take `finset.sum` over that instead of a `tsum` -/
theorem prob_event_eq_sum_of_support_subset [decidable_pred e] (s : finset α)
  (hs : oa.support ⊆ s) : ⦃e | oa⦄ = ∑ x in s, if x ∈ e then ⦃oa⦄ x else 0 :=
begin
  rw [prob_event_eq_tsum_ite],
  refine tsum_eq_sum (λ x hx, _),
  rw [eval_dist_eq_zero_of_not_mem_support (λ hx', hx $ finset.mem_coe.1 (hs hx')), if_t_t],
end

theorem prob_event_bind_eq_sum_of_support_subset (e : set β) (s : finset α) (hs : oa.support ⊆ s) :
  ⦃e | oa >>= ob⦄ = ∑ x in s, ⦃oa⦄ x * ⦃e | ob x⦄ :=
begin
  rw [prob_event_bind],
  refine tsum_eq_sum (λ x hx, _),
  rw [eval_dist_eq_zero_of_not_mem_support (λ h, hx (hs h)), zero_mul],
end

lemma prob_event_eq_sum_fin_support [spec.computable] [decidable_pred e] [oa.decidable] :
  ⦃e | oa⦄ = ∑ x in oa.fin_support, if x ∈ e then ⦃oa⦄ x else 0 :=
(prob_event_eq_sum_of_support_subset _ e oa.fin_support $ sorry ) --support_subset_fin_support oa)

@[simp] lemma prob_event_eq_zero_iff_disjoint_support : ⦃e | oa⦄ = 0 ↔ disjoint oa.support e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_zero_iff, support_eval_dist]

@[simp] lemma prob_event_eq_one_iff_support_subset : ⦃e | oa⦄ = 1 ↔ oa.support ⊆ e :=
by rw [prob_event.def, pmf.to_outer_measure_apply_eq_one_iff, support_eval_dist]

end support

lemma prob_event_eq_eval_dist_of_disjoint_sdiff_support [decidable_pred e] {a : α}
  (ha : a ∈ e) (h : disjoint (e \ {a}) oa.support) : ⦃e | oa⦄ = ⦃oa⦄ a :=
begin
  apply ⦃oa⦄.to_outer_measure_apply_eq_apply,
  sorry,
  sorry,
end

lemma prob_event_Union_eq_of_pairwise_disjoint (es : ℕ → set α) (h : pairwise (disjoint on es)) :
  ⦃⋃ i, es i | oa⦄ = ∑' i, ⦃es i | oa⦄ :=
begin
  sorry
  -- refine trans (prob_event_eq_to_nnreal_to_outer_measure_apply _ _) _,
  -- refine trans (congr_arg ennreal.to_nnreal $ 
  --     pmf.to_outer_measure_apply_Union ⦃oa⦄ h) _,
  -- refine trans (ennreal.tsum_to_nnreal_eq $ λ x, pmf.to_outer_measure_apply_ne_top _ _) _,
  -- refine tsum_congr (λ n, congr_arg ennreal.to_nnreal $ symm _),
  -- refine @pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ ⦃oa⦄ (es n)
  --   measurable_space.measurable_set_top,
end

lemma prob_event_union_eq_of_disjoint {e e' : set α} --[decidable_pred e] [decidable_pred e']
  (h : disjoint e e') : ⦃e ∪ e' | oa⦄ = ⦃e | oa⦄ + ⦃e' | oa⦄ :=
begin
  sorry,

  -- simp_rw [prob_event_eq_tsum_indicator],
  -- refine trans (tsum_congr (λ a, _))
  --   (tsum_add (⦃oa⦄.indicator_summable e) (⦃oa⦄.indicator_summable e')),
  -- by_cases ha : a ∈ e ∪ e',
  -- { by_cases ha' : a ∈ e,
  --   { have : a ∉ e' := set.disjoint_left.1 h ha',
  --     simp only [ha, ha', this, set.indicator_of_mem, set.indicator_of_not_mem,
  --       not_false_iff, add_zero]},
  --   { have : a ∈ e' := set.mem_union.elim ha (false.elim ∘ ha') id,
  --     simp only [ha, ha', this, set.indicator_of_mem, set.indicator_of_not_mem,
  --       not_false_iff, zero_add]} },
  -- { rw [set.indicator_of_not_mem ha, set.indicator_of_not_mem (ha ∘ (set.mem_union_left _)),
  --     set.indicator_of_not_mem (ha ∘ (set.mem_union_right _)), zero_add] }
end

lemma prob_event_eq_prob_event_inter_add_prob_event_diff {e s : set α} :
  ⦃e | oa⦄ = ⦃e ∩ s | oa⦄ + ⦃e \ s | oa⦄ :=
trans (by rw [set.inter_union_diff]) (prob_event_union_eq_of_disjoint oa $
  set.disjoint_of_subset_left (set.inter_subset_right _ _) (set.disjoint_diff))

end distribution_semantics