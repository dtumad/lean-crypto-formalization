import computational_monads.distribution_semantics.eval_distribution
import probability.independence

noncomputable theory

open oracle_comp oracle_spec
open_locale big_operators nnreal ennreal classical

variables {A B C : Type} {spec : oracle_spec} 
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
noncomputable example (oa : oracle_comp coin_oracle (fin 10)) :
  ℝ≥0∞ := ⦃ (>) 5 | oa ⦄

lemma prob_event_eq_to_outer_measure_apply (oa : oracle_comp spec A) (event : set A) :
  ⦃ event | oa ⦄ = ⦃oa⦄.to_outer_measure event :=
@pmf.to_measure_apply_eq_to_outer_measure_apply A ⊤
  ⦃oa⦄ event (measurable_space.measurable_set_top)

@[simp]
lemma eval_prob_eq_zero_iff_disjoint_support (oa : oracle_comp spec A) (event : set A) :
  ⦃ event | oa ⦄ = 0 ↔ disjoint oa.support event :=
by simp only [prob_event_eq_to_outer_measure_apply,
  pmf.to_outer_measure_apply_eq_zero_iff, support_eval_distribution]

@[simp]
lemma eval_prob_eq_one_iff_support_subset (oa : oracle_comp spec A) (event : set A) :
  ⦃ event | oa ⦄ = 1 ↔ oa.support ⊆ event :=
by simp only [prob_event_eq_to_outer_measure_apply,
  pmf.to_outer_measure_apply_eq_one_iff, support_eval_distribution]

@[simp]
lemma eval_prob_return (a : A) (event : set A) :
  ⦃ event | (return a : oracle_comp spec A) ⦄ = if a ∈ event then 1 else 0 :=
trans (prob_event_eq_to_outer_measure_apply _ event) (pmf.to_outer_measure_pure_apply a event)

lemma eval_prob_return_of_true (a : A) (event : set A) (ha : a ∈ event) :
  ⦃ event | (return a : oracle_comp spec A) ⦄ = 1 :=
by simp only [ha, eval_prob_return, if_true]

lemma eval_prob_return_of_false (a : A) (event : set A) (ha : a ∉ event) :
  ⦃ event | (return a : oracle_comp spec A) ⦄ = 0 :=
by simp only [ha, eval_prob_return, if_false]

@[simp]
lemma eval_prob_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (event : set B) :
  ⦃ event | oa >>= ob ⦄ = ∑' (a : A), ⦃oa⦄ a * ⦃ event | ob a ⦄ :=
begin
  simp only [prob_event, eval_distribution_bind, prob_event_eq_to_outer_measure_apply],
  refine pmf.to_outer_measure_bind_apply ⦃oa⦄ (λ a, ⦃ob a⦄) event,
end

@[simp]
lemma eval_prob_pure_bind (a : A) (ob : A → oracle_comp spec B) (event : set B) :
  ⦃ event | return a >>= ob ⦄ = ⦃ event | ob a ⦄ :=
begin
  simp only [eval_prob_bind, eval_distribution_return, pmf.pure_apply],
  refine trans (tsum_congr $ λ a', _) (tsum_ite_eq a ⦃ event | ob a⦄),
  split_ifs with h; simp [h],
end

@[simp]
lemma eval_prob_query (i : spec.ι) (t : spec.domain i) (event : set $ spec.range i) :
  ⦃ event | query i t ⦄ = fintype.card event / fintype.card (spec.range i) :=
trans (prob_event_eq_to_outer_measure_apply _ event) (pmf.to_outer_measure_uniform_of_fintype_apply event)

section indep_events

/-- Two collections of sets are independent if any two sets have intersection
  of probaility equal to the product of the individual probability.
  Independence is defined using a measure with `measurable_space` `⊤`.
  Further lemmas are written to be independent of this. -/
def indep_events (oa : oracle_comp spec A) (events events' : set (set A)) : Prop :=
@probability_theory.indep_sets A ⊤ events events' (@pmf.to_measure A ⊤ ⦃oa⦄)

variables (oa : oracle_comp spec A) (events events' : set (set A)) (e e' : set A)

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
def indep_event (oa : oracle_comp spec A) (e e' : set A) : Prop :=
indep_events oa {e} {e'}

variables (oa : oracle_comp spec A) (e e' : set A)

lemma indep_event_iff_indep_events : indep_event oa e e' ↔ indep_events oa {e} {e'} :=
iff.rfl

lemma indep_event_iff : indep_event oa e e' ↔ ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
by convert probability_theory.indep_sets_singleton_iff

lemma prob_event_inter_eq_mul_of_indep_event (h : indep_event oa e e') :
  ⦃ e ∩ e' | oa ⦄ = ⦃ e | oa ⦄ * ⦃ e' | oa ⦄ :=
(indep_event_iff oa e e').1 h

end indep_event