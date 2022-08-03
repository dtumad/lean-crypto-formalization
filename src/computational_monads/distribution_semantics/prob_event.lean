import computational_monads.distribution_semantics.equiv
import probability.independence

namespace distribution_semantics

open oracle_comp
open_locale big_operators nnreal ennreal

variables {α β γ : Type} {spec spec' : oracle_spec} 
variable [spec.finite_range]
variable [spec'.finite_range]

/-- Probability of a predicate holding after running a particular experiment.
  Defined in terms of the outer measure associated to the corresponding `pmf`.

  The initial definition uses a `measure` to access more general lemmas,
    but is equal to the `outer_measure` (see `prob_event_eq_to_outer_measure_apply`)
  TODO : renaming -/
noncomputable def prob_event {α : Type} (oa : oracle_comp spec α) (event : set α) : ℝ≥0∞ :=
@pmf.to_measure α ⊤ ⦃oa⦄ event

notation `⦃` event `|` oa `⦄` := prob_event oa event

/-- Probability that the result of a computation is greater than `5` -/
noncomputable example (oa : oracle_comp oracle_spec.coin_oracle (fin 10)) :
  ℝ≥0∞ := ⦃(>) 5 | oa⦄

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (a a' : α)
  (e e' : set α) (e'' : set β)

lemma prob_event_eq_of_equiv {oa : oracle_comp spec α} {oa' : oracle_comp spec' α}
  (h : oa ≃ₚ oa') (e : set α) : ⦃e | oa⦄ = ⦃e | oa'⦄ :=
by simp_rw [prob_event, h]

lemma prob_event_eq_to_outer_measure_apply : ⦃e | oa⦄ = ⦃oa⦄.to_outer_measure e :=
@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤
  ⦃oa⦄ e (measurable_space.measurable_set_top)

lemma prob_event_eq_tsum [decidable_pred e] : ⦃e | oa⦄ = ∑' x, if x ∈ e then ⦃oa⦄ x else 0 :=
by simp only [prob_event_eq_to_outer_measure_apply,
  pmf.to_outer_measure_apply, set.indicator_apply]

section pure

@[simp]
lemma prob_event_pure [decidable_pred e] :
  ⦃ e | (pure a : oracle_comp spec α) ⦄ = if a ∈ e then 1 else 0 :=
(trans (prob_event_eq_to_outer_measure_apply _ e) $
  (pmf.to_outer_measure_pure_apply a e).trans (by congr))

lemma prob_event_pure_of_true [decidable_pred e] (ha : a ∈ e) :
  ⦃ e | (pure a : oracle_comp spec α) ⦄ = 1 :=
by simp only [ha, prob_event_pure, if_true]

lemma prob_event_pure_of_false [decidable_pred e] (ha : a ∉ e) :
  ⦃ e | (pure a : oracle_comp spec α) ⦄ = 0 :=
by simp only [ha, prob_event_pure, if_false]

end pure

section bind

@[simp]
lemma prob_event_bind : ⦃e'' | oa >>= ob⦄ = ∑' (a : α), ⦃oa⦄ a * ⦃e'' | ob a⦄ :=
begin
  simp only [prob_event, eval_distribution_bind, prob_event_eq_to_outer_measure_apply],
  exact pmf.to_outer_measure_bind_apply ⦃oa⦄ (λ a, ⦃ob a⦄) e'',
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
trans (prob_event_eq_to_outer_measure_apply _ e)
  ((pmf.to_outer_measure_uniform_of_fintype_apply e).trans (by congr))

end query

section map

-- @[simp]
-- lemma prob_event_map (f : α → β) (e : set β) :
--   ⦃e | f <$> oa⦄ = ⦃e ∘ f | oa⦄ :=
-- begin
--   simp_rw [prob_event_eq_to_outer_measure_apply],
--   simp_rw [functor.map, bind'_eq_bind],
--   simp_rw [bind_pure],
-- end

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

lemma prob_event_eq_sum_fin_support [spec.computable] [decidable_pred e] (hoa : oa.decidable) :
  ⦃ e | oa ⦄ = ∑ x in (oa.fin_support hoa), if x ∈ e then ⦃oa⦄ x else 0 :=
(prob_event_eq_sum_of_support_subset e (oa.fin_support hoa) $ support_subset_fin_support oa hoa)

@[simp]
lemma prob_event_eq_zero_iff_disjoint_support : ⦃ e | oa ⦄ = 0 ↔ disjoint oa.support e :=
by simp only [prob_event_eq_to_outer_measure_apply,
  pmf.to_outer_measure_apply_eq_zero_iff, support_eval_distribution]

@[simp]
lemma prob_event_eq_one_iff_support_subset : ⦃ e | oa ⦄ = 1 ↔ oa.support ⊆ e :=
by simp only [prob_event_eq_to_outer_measure_apply,
  pmf.to_outer_measure_apply_eq_one_iff, support_eval_distribution]

end support

-- TODO: seperate `indep` file?
section indep_events

/-- Two collections of sets are independent if any two sets have intersection
  of probaility equal to the product of the individual probability.
  Independence is defined using a measure with `measurable_space` `⊤`.
  Further lemmas are written to be independent of this. -/
def indep_events (oa : oracle_comp spec α) (events events' : set (set α)) : Prop :=
@probability_theory.indep_sets α ⊤ events events' (@pmf.to_measure α ⊤ ⦃oa⦄)

variables (events events' : set (set α))

lemma indep_events_iff : indep_events oa events events' ↔ ∀ e e', e ∈ events → e' ∈ events' →
  ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
iff.rfl

lemma prob_event_inter_eq_mul_of_indep_events (h : indep_events oa events events')
  (he : e ∈ events) (he' : e' ∈ events') : ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
h e e' he he'

end indep_events

section indep_event

/-- To events are independent if the prob of the intersection equals product of individual probs.
  Equivalent to `indep_events` with singleton collections of sets-/
def indep_event (oa : oracle_comp spec α) (e e' : set α) : Prop :=
indep_events oa {e} {e'}

lemma indep_event_iff_indep_events : indep_event oa e e' ↔ indep_events oa {e} {e'} :=
iff.rfl

lemma indep_event_iff : indep_event oa e e' ↔ ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
by convert probability_theory.indep_sets_singleton_iff

lemma prob_event_inter_eq_mul_of_indep_event (h : indep_event oa e e') :
  ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
(indep_event_iff oa e e').1 h

end indep_event

end distribution_semantics