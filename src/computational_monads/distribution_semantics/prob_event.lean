import computational_monads.distribution_semantics.eval_distribution
import probability.independence

-- noncomputable theory

namespace distribution_semantics

open oracle_comp
open_locale big_operators nnreal ennreal

variables {α β γ : Type} {spec : oracle_spec} 
variable [spec.finite_range]

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
  ℝ≥0∞ := ⦃ (>) 5 | oa ⦄

variables (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (a a' : α)
  (e e' : set α) (e'' : set β)

lemma prob_event_eq_to_outer_measure_apply : ⦃ e | oa ⦄ = ⦃oa⦄.to_outer_measure e :=
@pmf.to_measure_apply_eq_to_outer_measure_apply α ⊤
  ⦃oa⦄ e (measurable_space.measurable_set_top)

@[simp]
lemma eval_prob_eq_zero_iff_disjoint_support : ⦃ e | oa ⦄ = 0 ↔ disjoint oa.support e :=
by simp only [prob_event_eq_to_outer_measure_apply,
  pmf.to_outer_measure_apply_eq_zero_iff, support_eval_distribution]

@[simp]
lemma eval_prob_eq_one_iff_support_subset : ⦃ e | oa ⦄ = 1 ↔ oa.support ⊆ e :=
by simp only [prob_event_eq_to_outer_measure_apply,
  pmf.to_outer_measure_apply_eq_one_iff, support_eval_distribution]

@[simp]
lemma eval_prob_return [decidable_pred e] :
  ⦃ e | (return a : oracle_comp spec α) ⦄ = if a ∈ e then 1 else 0 :=
(trans (prob_event_eq_to_outer_measure_apply _ e) $
  (pmf.to_outer_measure_pure_apply a e).trans (by congr))

lemma eval_prob_return_of_true [decidable_pred e] (ha : a ∈ e) :
  ⦃ e | (return a : oracle_comp spec α) ⦄ = 1 :=
by simp only [ha, eval_prob_return, if_true]

lemma eval_prob_return_of_false [decidable_pred e] (ha : a ∉ e) :
  ⦃ e | (return a : oracle_comp spec α) ⦄ = 0 :=
by simp only [ha, eval_prob_return, if_false]

@[simp]
lemma eval_prob_bind : ⦃ e'' | oa >>= ob ⦄ = ∑' (a : α), ⦃oa⦄ a * ⦃ e'' | ob a ⦄ :=
begin
  simp only [prob_event, eval_distribution_bind, prob_event_eq_to_outer_measure_apply],
  exact pmf.to_outer_measure_bind_apply ⦃oa⦄ (λ a, ⦃ob a⦄) e'',
end

@[simp]
lemma eval_prob_pure_bind [decidable_eq α] :
  ⦃ e'' | return a >>= ob ⦄ = ⦃ e'' | ob a ⦄ :=
begin
  simp only [eval_prob_bind, eval_distribution_return, pmf.pure_apply],
  refine trans (tsum_congr $ λ a', _) (tsum_ite_eq a ⦃ e'' | ob a⦄),
  split_ifs with h; simp [h],
end

@[simp]
lemma eval_prob_query (i : spec.ι) (t : spec.domain i) (e : set $ spec.range i)
  [decidable_pred e] : ⦃ e | query i t ⦄ = fintype.card e / fintype.card (spec.range i) :=
trans (prob_event_eq_to_outer_measure_apply _ e)
  ((pmf.to_outer_measure_uniform_of_fintype_apply e).trans (by congr))

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