import computational_monads.distribution_semantics.equiv
import probability.independence
import to_mathlib.pmf_stuff

/-!
# Probability of Events

This file defines the probability of some event holding after running a computation.
The definition is in terms of the `measure` associated to the `pmf` given by `eval_dist`.

This definition is equivalent to one in terms of summations, in particular an infinite `tsum`.
If the support is decidable, we can instead give an expression in terms of `finset.sum`
-/

namespace distribution_semantics

open oracle_comp
open_locale big_operators nnreal ennreal

variables {α β γ ι : Type} {spec spec' : oracle_spec} 
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (a a' : α)
  (e e' : set α) (e'' : set β)
variable [spec.finite_range]
variable [spec'.finite_range]

/-- Probability of a predicate holding after running a particular experiment.
Defined in terms of the outer measure associated to the corresponding `pmf`.
The initial definition uses a `measure` to access more general lemmas,
  but is equal to the `outer_measure` (see `prob_event_eq_to_outer_measure_apply`). -/
noncomputable def prob_event {α : Type} (oa : oracle_comp spec α) (event : set α) : ℝ≥0 :=
ennreal.to_nnreal (@pmf.to_measure α ⊤ ⦃oa⦄ event)

notation `⦃` event `|` oa `⦄` := prob_event oa event

/-- Probability that the result of a computation is greater than `5` -/
noncomputable example (oa : oracle_comp oracle_spec.coin_oracle (fin 10)) :
  ℝ≥0∞ := ⦃(>) 5 | oa⦄

lemma prob_event_eq_to_nnreal_to_outer_measure_apply :
  ⦃e | oa⦄ = (⦃oa⦄.to_outer_measure e).to_nnreal :=
congr_arg ennreal.to_nnreal (@pmf.to_measure_apply_eq_to_outer_measure_apply
  α ⊤ _ e (measurable_space.measurable_set_top))

lemma prob_event_eq_to_nnreal_to_measure_apply :
  ⦃e | oa⦄ = (@pmf.to_measure α ⊤ ⦃oa⦄ e).to_nnreal := rfl

lemma coe_prob_event_eq_to_outer_measure_apply : (⦃e | oa⦄ : ℝ≥0∞) = ⦃oa⦄.to_outer_measure e :=
(ennreal.coe_to_nnreal $ @pmf.to_measure_apply_ne_top α ⊤ ⦃oa⦄ e).trans
  (@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ _ e (measurable_space.measurable_set_top))

/-- Probability of an event in terms of non-decidable `set.indicator` sum -/
lemma prob_event_eq_tsum_indicator : ⦃e | oa⦄ = ∑' x, e.indicator ⦃oa⦄ x :=
begin
  rw [prob_event_eq_to_nnreal_to_outer_measure_apply],
  have := pmf.to_outer_measure_apply ⦃oa⦄ e,
  refine (congr_arg ennreal.to_nnreal this).trans _,
  refine trans (congr_arg ennreal.to_nnreal _) (ennreal.to_nnreal_coe),
  rw [ennreal.coe_tsum],
  simp_rw ennreal.coe_indicator,
  exact nnreal.indicator_summable ⦃oa⦄.summable_coe e
end

/-- Probability of an event in terms of a decidable `ite` sum-/
lemma prob_event_eq_tsum [decidable_pred (∈ e)] : ⦃e | oa⦄ = ∑' x, if x ∈ e then ⦃oa⦄ x else 0 :=
begin
  refine (prob_event_eq_tsum_indicator oa e).trans (tsum_congr $ λ x, _),
  unfold set.indicator, congr,
end

lemma prob_event_eq_of_equiv {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') (e : set α) : ⦃e | oa⦄ = ⦃e | oa'⦄ :=
by simp_rw [prob_event, h]

lemma prob_event_eq_iff_to_outer_measure_apply_eq {oa : oracle_comp spec α} (e e' : set α) :
  ⦃e | oa⦄ = ⦃e' | oa⦄ ↔ ⦃oa⦄.to_outer_measure e = ⦃oa⦄.to_outer_measure e' :=
by simp_rw [prob_event_eq_to_nnreal_to_outer_measure_apply, ennreal.to_nnreal_eq_to_nnreal_iff,
  pmf.to_outer_measure_apply_ne_top, and_false, false_and, or_false]

lemma prob_event_eq_mul_iff_to_outer_measure_apply_eq {oa : oracle_comp spec α} (e e' e'' : set α) :
  ⦃e | oa⦄ = ⦃e' | oa⦄ * ⦃e'' | oa⦄ ↔
    ⦃oa⦄.to_outer_measure e = (⦃oa⦄.to_outer_measure e') * (⦃oa⦄.to_outer_measure e'') :=
begin
  simp_rw [prob_event_eq_to_nnreal_to_outer_measure_apply],
  rw [← ennreal.to_nnreal_mul, ennreal.to_nnreal_eq_to_nnreal_iff'],
  { exact pmf.to_outer_measure_apply_ne_top ⦃oa⦄ e },
  { refine ennreal.mul_ne_top _ _; apply pmf.to_outer_measure_apply_ne_top }
end

lemma prob_event_eq_mul_iff_to_measure_apply_eq {oa : oracle_comp spec α} (e e' e'' : set α) :
  ⦃e | oa⦄ = ⦃e' | oa⦄ * ⦃e'' | oa⦄ ↔
    @pmf.to_measure α ⊤ ⦃oa⦄ e = (@pmf.to_measure α ⊤ ⦃oa⦄ e') * (@pmf.to_measure α ⊤ ⦃oa⦄ e'') :=
begin
  rw [prob_event_eq_mul_iff_to_outer_measure_apply_eq,
    pmf.to_measure_apply_eq_to_outer_measure_apply, pmf.to_measure_apply_eq_to_outer_measure_apply,
      pmf.to_measure_apply_eq_to_outer_measure_apply];
  exact measurable_space.measurable_set_top,
end

section pure

lemma prob_event_pure_eq_indicator :
  ⦃e | (pure a : oracle_comp spec α)⦄ = e.indicator (λ _, (1 : ℝ≥0)) a :=
begin
  refine trans (prob_event_eq_to_nnreal_to_outer_measure_apply _ e) _,
  refine trans (congr_arg ennreal.to_nnreal $ pmf.to_outer_measure_pure_apply a e) _,
  split_ifs with h; simp [h],
end

@[simp]
lemma prob_event_pure [decidable_pred (∈ e)] :
  ⦃e | (pure a : oracle_comp spec α)⦄ = if a ∈ e then 1 else 0 :=
begin
  refine trans (prob_event_pure_eq_indicator a e) _,
  split_ifs with ha; simp [ha],
end

lemma prob_event_pure_of_true (ha : a ∈ e) :
  ⦃ e | (pure a : oracle_comp spec α) ⦄ = 1 :=
by simp only [ha, prob_event_pure_eq_indicator, set.indicator_of_mem]

lemma prob_event_pure_of_false (ha : a ∉ e) :
  ⦃ e | (pure a : oracle_comp spec α) ⦄ = 0 :=
by simp only [ha, prob_event_pure_eq_indicator, set.indicator_of_not_mem, not_false_iff]

end pure

section bind

@[simp]
lemma prob_event_bind : ⦃e'' | oa >>= ob⦄ = ∑' (a : α), ⦃oa⦄ a * ⦃e'' | ob a⦄ :=
calc ⦃e'' | oa >>= ob⦄
  = (⦃oa >>= ob⦄.to_outer_measure e'').to_nnreal :
    prob_event_eq_to_nnreal_to_outer_measure_apply _ _
  ... = (∑' (a : α), ↑(⦃oa⦄ a) * (⦃ob a⦄.to_outer_measure e'')).to_nnreal : congr_arg
    ennreal.to_nnreal (by erw [eval_dist_bind, pmf.to_outer_measure_bind_apply])
  ... = ∑' (a : α), (↑(⦃oa⦄ a) * (⦃ob a⦄.to_outer_measure e'')).to_nnreal :
    ennreal.tsum_to_nnreal_eq begin
      refine λ x, _,
      refine ennreal.mul_ne_top _ _,
      {
        refine ennreal.coe_ne_top,
      },
      {
        refine pmf.to_outer_measure_apply_ne_top _ _,
      }
    end
  ... = ∑' (a : α), ⦃oa⦄ a * ⦃e'' | ob a⦄ : tsum_congr (λ a, by rw [ennreal.to_nnreal_mul,
    ennreal.to_nnreal_coe, prob_event_eq_to_nnreal_to_outer_measure_apply])

@[simp]
lemma prob_event_pure_bind : ⦃e'' | pure a >>= ob⦄ = ⦃e'' | ob a⦄ :=
prob_event_eq_of_equiv (pure_bind_equiv ob a) e''

@[simp]
lemma prob_event_bind_pure :
  ⦃e | oa >>= pure ⦄ = ⦃e | oa⦄ :=
prob_event_eq_of_equiv (bind_pure_equiv oa) e

end bind

section query

@[simp]
lemma prob_event_query (i : spec.ι) (t : spec.domain i) (e : set $ spec.range i)
  [decidable_pred e] : ⦃ e | query i t ⦄ = fintype.card e / fintype.card (spec.range i) :=
begin
  refine trans (prob_event_eq_to_nnreal_to_outer_measure_apply _ e) _,
  rw [eval_dist_query],
  rw [pmf.to_outer_measure_uniform_of_fintype_apply],
  simp_rw [ennreal.to_nnreal_div, ennreal.to_nnreal_nat],
  congr,
end

end query

section map

@[simp]
lemma prob_event_map (f : α → β) (e : set β) :
  ⦃e | f <$> oa⦄ = ⦃f ⁻¹' e | oa⦄ :=
by simp only [prob_event_eq_to_nnreal_to_outer_measure_apply,
  eval_dist_map, pmf.to_outer_measure_map_apply]

end map

section support

/-- Given a `finset` containing the `support` of some `oracle_comp`,
  it suffices to take `finset.sum` over that instead of a `tsum` -/
theorem prob_event_eq_sum_of_support_subset {oa : oracle_comp spec α} [decidable_pred e]
  (s : finset α) (hs : oa.support ⊆ s) :
  ⦃e | oa⦄ = ∑ x in s, if x ∈ e then ⦃oa⦄ x else 0 :=
begin
  refine trans (prob_event_eq_tsum oa e) (tsum_eq_sum (λ a ha, _)),
  have : ⦃oa⦄ a = 0 := eval_dist_eq_zero_of_not_mem_support (λ h, ha (hs h)),
  simp only [this, ennreal.coe_zero, if_t_t],
end

lemma prob_event_eq_sum_fin_support [spec.computable] [decidable_pred e] [oa.decidable] :
  ⦃ e | oa ⦄ = ∑ x in oa.fin_support, if x ∈ e then ⦃oa⦄ x else 0 :=
(prob_event_eq_sum_of_support_subset e oa.fin_support $ support_subset_fin_support oa)

@[simp]
lemma prob_event_eq_zero_iff_disjoint_support : ⦃e | oa⦄ = 0 ↔ disjoint oa.support e :=
begin
  refine (ennreal.to_nnreal_eq_zero_iff _).trans _,
  simp only [pmf.to_measure_apply_ne_top, or_false],
  refine (@pmf.to_measure_apply_eq_iff_to_outer_measure_apply_eq
    α ⊤ ⦃oa⦄ 0 e measurable_space.measurable_set_top).trans _,
  rw [← support_eval_dist],
  exact (⦃oa⦄.to_outer_measure_apply_eq_zero_iff e),
end

@[simp]
lemma prob_event_eq_one_iff_support_subset : ⦃e | oa⦄ = 1 ↔ oa.support ⊆ e :=
begin
  refine (ennreal.to_nnreal_eq_one_iff _).trans _,
  refine (@pmf.to_measure_apply_eq_iff_to_outer_measure_apply_eq
    α ⊤ ⦃oa⦄ 1 e measurable_space.measurable_set_top).trans _,
  rw [← support_eval_dist],
  exact (⦃oa⦄.to_outer_measure_apply_eq_one_iff e),
end

end support

lemma prob_event_eq_eval_dist_of_disjoint_sdiff_support [decidable_pred e] {a : α}
  (ha : a ∈ e) (h : disjoint (e \ {a}) oa.support) : ⦃e | oa⦄ = ⦃oa⦄ a :=
begin
  refine (prob_event_eq_tsum oa e).trans ((tsum_eq_single a $ λ a' ha', _).trans (if_pos ha)),
  split_ifs with hae,
  { exact (eval_dist_eq_zero_of_not_mem_support
      (set.disjoint_left.1 h $ set.mem_diff_of_mem hae ha')) },
  { exact rfl }
end

lemma prob_event_Union_eq_of_pairwise_disjoint (es : ℕ → set α) (h : pairwise (disjoint on es)) :
  ⦃⋃ i, es i | oa⦄ = ∑' i, ⦃es i | oa⦄ :=
begin
  refine trans (prob_event_eq_to_nnreal_to_outer_measure_apply _ _) _,
  refine trans (congr_arg ennreal.to_nnreal $ 
      pmf.to_outer_measure_apply_Union ⦃oa⦄ h) _,
  refine trans (ennreal.tsum_to_nnreal_eq $ λ x, pmf.to_outer_measure_apply_ne_top _ _) _,
  refine tsum_congr (λ n, congr_arg ennreal.to_nnreal $ symm _),
  refine @pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤ ⦃oa⦄ (es n)
    measurable_space.measurable_set_top,
end

lemma prob_event_union_eq_of_disjoint {e e' : set α} [decidable_pred e] [decidable_pred e']
  (h : disjoint e e') : ⦃e ∪ e' | oa⦄ = ⦃e | oa⦄ + ⦃e' | oa⦄ :=
begin
  simp_rw [prob_event_eq_tsum_indicator],
  refine trans (tsum_congr (λ a, _))
    (tsum_add (⦃oa⦄.indicator_summable e) (⦃oa⦄.indicator_summable e')),
  by_cases ha : a ∈ e ∪ e',
  { by_cases ha' : a ∈ e,
    { have : a ∉ e' := set.disjoint_left.1 h ha',
      simp only [ha, ha', this, set.indicator_of_mem, set.indicator_of_not_mem,
        not_false_iff, add_zero]},
    { have : a ∈ e' := set.mem_union.elim ha (false.elim ∘ ha') id,
      simp only [ha, ha', this, set.indicator_of_mem, set.indicator_of_not_mem,
        not_false_iff, zero_add]} },
  { rw [set.indicator_of_not_mem ha, set.indicator_of_not_mem (ha ∘ (set.mem_union_left _)),
      set.indicator_of_not_mem (ha ∘ (set.mem_union_right _)), zero_add] }
end

section prod

lemma prob_event_diagonal [hα : decidable_eq α] (oa : oracle_comp spec (α × α)) :
  ⦃set.diagonal α | oa⦄ = ∑' (a : α), ⦃oa⦄ (a, a) :=
calc ⦃set.diagonal α | oa⦄ = ∑' (x : α × α), ite (x ∈ set.diagonal α) (⦃oa⦄ x) 0 :
    prob_event_eq_tsum oa (set.diagonal α)
  ... = ∑' (a a' : α), ite (a = a') (⦃oa⦄ (a, a')) 0 :
    begin
      refine tsum_prod' _ _,
      { refine nnreal.summable_of_le (λ x, _) ⦃oa⦄.summable_coe,
        split_ifs; simp only [le_rfl, zero_le'] },
      { have : summable (λ a, ⦃oa⦄ (a, a)),
        from nnreal.summable_comp_injective ⦃oa⦄.summable_coe
          (λ x y hxy, (prod.eq_iff_fst_eq_snd_eq.1 hxy).1),
        refine λ a, nnreal.summable_of_le (λ a', _) this,
        split_ifs,
        { simp only [set.mem_diagonal_iff] at h,
          exact h ▸ le_rfl },
        { exact zero_le' } }
    end
  ... = ∑' (a a' : α), ite (a = a') (⦃oa⦄ (a, a)) 0 :
    tsum_congr (λ a, tsum_congr (λ a', by by_cases h : a = a'; simp only [h, if_false]))
  ... = ∑' (a a' : α), ite (a' = a) (⦃oa⦄ (a, a)) 0 : by simp_rw [@eq_comm]
  ... = ∑' (a : α), ⦃oa⦄ (a, a) : tsum_congr (λ a, tsum_ite_eq _ _) 

end prod

end distribution_semantics