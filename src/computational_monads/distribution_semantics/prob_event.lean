import computational_monads.distribution_semantics.equiv
import probability.independence
import to_mathlib.pmf_stuff

namespace distribution_semantics

open oracle_comp
open_locale big_operators nnreal ennreal

variables {α β γ ι : Type} {spec spec' : oracle_spec} 
variable [spec.finite_range]
variable [spec'.finite_range]

/-- Probability of a predicate holding after running a particular experiment.
  Defined in terms of the outer measure associated to the corresponding `pmf`.

  The initial definition uses a `measure` to access more general lemmas,
    but is equal to the `outer_measure` (see `prob_event_eq_to_outer_measure_apply`). -/

-- noncomputable def prob_event {α : Type} (oa : oracle_comp spec α) (event : set α) : ℝ≥0∞ :=
-- @pmf.to_measure α ⊤ ⦃oa⦄ event

noncomputable def prob_event {α : Type} (oa : oracle_comp spec α) (event : set α) : ℝ≥0 :=
ennreal.to_nnreal (@pmf.to_measure α ⊤ ⦃oa⦄ event)

notation `⦃` event `|` oa `⦄` := prob_event oa event

/-- Probability that the result of a computation is greater than `5` -/
noncomputable example (oa : oracle_comp oracle_spec.coin_oracle (fin 10)) :
  ℝ≥0∞ := ⦃(>) 5 | oa⦄

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (a a' : α)
  (e e' : set α) (e'' : set β)

lemma prob_event_eq_of_equiv {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') (e : set α) : ⦃e | oa⦄ = ⦃e | oa'⦄ :=
by simp_rw [prob_event, h]

lemma prob_event_eq_to_nnreal_to_outer_measure_apply :
  ⦃e | oa⦄ = (⦃oa⦄.to_outer_measure e).to_nnreal :=
congr_arg ennreal.to_nnreal (@pmf.to_measure_apply_eq_to_outer_measure_apply
  α ⊤ _ e (measurable_space.measurable_set_top))

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
  refine (prob_event_eq_tsum_indicator oa e).trans _,
  refine tsum_congr (λ x, _),
  rw [set.indicator],
  split_ifs; refl,
end

section pure

lemma prob_event_pure_eq_indicator : ⦃e | (pure a : oracle_comp spec α)⦄ = e.indicator (λ _, (1 : ℝ≥0)) a :=
begin
  refine trans (prob_event_eq_to_nnreal_to_outer_measure_apply _ e) _,
  refine trans (congr_arg ennreal.to_nnreal $ pmf.to_outer_measure_pure_apply a e) _,
  refine (ennreal.ite_to_nnreal _ _ _),
end

@[simp]
lemma prob_event_pure [decidable_pred (∈ e)] :
  ⦃e | (pure a : oracle_comp spec α)⦄ = if a ∈ e then 1 else 0 :=
begin
  refine trans (prob_event_pure_eq_indicator a e) _,
  split_ifs with ha; simp [ha],
end

lemma prob_event_pure_of_true [decidable_pred (∈ e)] (ha : a ∈ e) :
  ⦃ e | (pure a : oracle_comp spec α) ⦄ = 1 :=
by simp only [ha, prob_event_pure, if_true]

lemma prob_event_pure_of_false [decidable_pred (∈ e)] (ha : a ∉ e) :
  ⦃ e | (pure a : oracle_comp spec α) ⦄ = 0 :=
by simp only [ha, prob_event_pure, if_false]

end pure

section bind

@[simp]
lemma prob_event_bind : ⦃e'' | oa >>= ob⦄ = ∑' (a : α), ⦃oa⦄ a * ⦃e'' | ob a⦄ :=
calc ⦃e'' | oa >>= ob⦄
  = ∑' (b : β), e''.indicator ⦃oa >>= ob⦄ b : begin
    apply prob_event_eq_tsum_indicator,
  end
  ... = ∑' (b : β) (a : α), ⦃oa⦄ a * (e''.indicator ⦃ob a⦄ b) : begin
    refine tsum_congr (λ b, _),
    by_cases hb : b ∈ e'',
    {
      simp only [set.indicator_of_mem hb, eval_distribution_bind_apply],
    },
    {
      simp only [set.indicator_of_not_mem hb, mul_zero, tsum_zero]
    }
  end
  ... = ∑' (a : α) (b : β), ⦃oa⦄ a * (e''.indicator ⦃ob a⦄ b) : begin
    refine tsum_comm' sorry sorry _,
    {
      refine λ b, _,
      
      refine nnreal.summable_of_le _ (⦃oa⦄.summable_coe),
      refine (λ a, _),
      refine le_of_le_of_eq (mul_le_mul le_rfl _ zero_le' zero_le') (mul_one _),
      refine set.indicator_apply_le (λ _, _),
      refine pmf.apply_le_one ⦃ob a⦄ b,
    }
  end
  ... = ∑' (a : α), ⦃oa⦄ a * ∑' (b : β), (e''.indicator ⇑⦃ob a⦄ b) : begin
    refine tsum_congr (λ a, _),
    rw [← nnreal.tsum_mul_left],
  end
  ... = ∑' (a : α), ⦃oa⦄ a * ⦃e'' | ob a⦄ : begin
    simp_rw [prob_event_eq_tsum_indicator],
  end

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
  rw [eval_distribution_query],
  rw [pmf.to_outer_measure_uniform_of_fintype_apply],
  simp_rw [ennreal.to_nnreal_div, nat.cast_to_nnreal],
  congr,
end

-- trans (prob_event_eq_to_outer_measure_apply _ e)
--   ((pmf.to_outer_measure_uniform_of_fintype_apply e).trans (by congr))

end query

section map

@[simp]
lemma prob_event_map (f : α → β) (e : set β) :
  ⦃e | f <$> oa⦄ = ⦃f ⁻¹' e | oa⦄ :=
by simp only [prob_event_eq_to_nnreal_to_outer_measure_apply,
  eval_distribution_map, pmf.to_outer_measure_map_apply]

end map

section support

/-- Given a `finset` containing the `support` of some `oracle_comp`,
  it suffices to take `finset.sum` over that instead of a `tsum` -/
theorem prob_event_eq_sum_of_support_subset {oa : oracle_comp spec α} [decidable_pred e]
  (s : finset α) (hs : oa.support ⊆ s) :
  ⦃e | oa⦄ = ∑ x in s, if x ∈ e then ⦃oa⦄ x else 0 :=
begin
  refine trans (prob_event_eq_tsum oa e) (tsum_eq_sum (λ a ha, _)),
  have : ⦃oa⦄ a = 0 := eval_distribution_eq_zero_of_not_mem_support (λ h, ha (hs h)),
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
  rw [← support_eval_distribution],
  exact (⦃oa⦄.to_outer_measure_apply_eq_zero_iff e),
end

@[simp]
lemma prob_event_eq_one_iff_support_subset : ⦃e | oa⦄ = 1 ↔ oa.support ⊆ e :=
begin
  refine (ennreal.to_nnreal_eq_one_iff _).trans _,
  refine (@pmf.to_measure_apply_eq_iff_to_outer_measure_apply_eq
    α ⊤ ⦃oa⦄ 1 e measurable_space.measurable_set_top).trans _,
  rw [← support_eval_distribution],
  exact (⦃oa⦄.to_outer_measure_apply_eq_one_iff e),
end

end support

lemma prob_event_eq_eval_distribution_of_disjoint_sdiff_support [decidable_pred e] {a : α}
  (ha : a ∈ e) (h : disjoint (e \ {a}) oa.support) : ⦃e | oa⦄ = ⦃oa⦄ a :=
sorry
-- begin
--   refine (prob_event_eq_tsum oa e).trans ((tsum_eq_single a $ λ a' ha', _).trans (if_pos ha)),
--   split_ifs with hae,
--   { exact ennreal.coe_eq_zero.2 (eval_distribution_eq_zero_of_not_mem_support
--       (set.disjoint_left.1 h $ set.mem_diff_of_mem hae ha')) },
--   { exact rfl }
-- end

lemma prob_event_Union_eq_of_pairwise_disjoint (es : ℕ → set α) (h : pairwise (disjoint on es)) :
  ⦃⋃ i, es i | oa⦄ = ∑' i, ⦃es i | oa⦄ :=
sorry
-- begin
--   rw [prob_event_eq_to_outer_measure_apply],
--   refine (measure_theory.outer_measure.Union_eq_of_caratheodory _
--     (λ n, pmf.measurable_set_to_outer_measure_caratheodory _ (es n)) h).trans
--       (tsum_congr (λ n, symm $ prob_event_eq_to_outer_measure_apply oa (es n))),
-- end

lemma prob_event_union_eq_of_disjoint {e e' : set α} [decidable_pred e] [decidable_pred e']
  (h : disjoint e e') : ⦃e ∪ e' | oa⦄ = ⦃e | oa⦄ + ⦃e' | oa⦄ :=
sorry
-- begin
--   simp_rw [prob_event_eq_tsum],
--   refine trans (tsum_congr (λ a, _)) (tsum_add ennreal.summable ennreal.summable),
--   by_cases ha : a ∈ e ∪ e',
--   { by_cases ha' : a ∈ e,
--     { have : a ∉ e' := set.disjoint_left.1 h ha',
--       simp_rw [ha, ha', this, if_true, if_false, add_zero] },
--     { have : a ∈ e' := set.mem_union.elim ha (false.elim ∘ ha') id,
--       simp_rw [ha, ha', this, if_true, if_false, zero_add] }
--   },
--   { simp_rw [ha, ha ∘ (set.mem_union_left _), ha ∘ (set.mem_union_right _), if_false, zero_add] }
-- end

-- TODO: seperate `indep` file?
section indep_events

/-- Two collections of sets are independent if any two sets have intersection
  of probaility equal to the product of the individual probability.
  Independence is defined using a measure with `measurable_space` `⊤`.
  Further lemmas are written to be independent of this. -/
def indep_events (oa : oracle_comp spec α) (events events' : set (set α)) : Prop :=
@probability_theory.indep_sets α ⊤ events events' (@pmf.to_measure α ⊤ ⦃oa⦄)

variables (events events' : set (set α))

lemma indep_events_iff : indep_events oa events events' ↔
  ∀ e e', e ∈ events → e' ∈ events' → ⦃e ∩ e' | oa⦄ = ⦃e | oa⦄ * ⦃e' | oa⦄ :=
begin
  rw [indep_events, probability_theory.indep_sets],
  sorry
end


lemma prob_event_inter_eq_mul_of_indep_events (h : indep_events oa events events')
  (he : e ∈ events) (he' : e' ∈ events') : ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
(indep_events_iff oa events events').1 h e e' he he'

end indep_events

section indep_event

/-- To events are independent if the prob of the intersection equals product of individual probs.
  Equivalent to `indep_events` with singleton collections of sets-/
def indep_event (oa : oracle_comp spec α) (e e' : set α) : Prop :=
indep_events oa {e} {e'}

lemma indep_event_iff_indep_events : indep_event oa e e' ↔ indep_events oa {e} {e'} :=
iff.rfl

lemma indep_event_iff : indep_event oa e e' ↔ ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
sorry -- by convert probability_theory.indep_sets_singleton_iff

lemma prob_event_inter_eq_mul_of_indep_event (h : indep_event oa e e') :
  ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
(indep_event_iff oa e e').1 h

end indep_event

end distribution_semantics