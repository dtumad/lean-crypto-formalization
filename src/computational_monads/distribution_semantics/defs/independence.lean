/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.defs.prob_event
import probability.independence.basic

/-!
# Independent Events for Oracle Computations

Defines to types of independence for events after an `oracle_comp`,
  corresponding to mathlibs two measure-theoretic indepence definitions.
`indep_events` says that all events in a set are independent of each other.
`indep_event` says that two particular events are independent for the computation.
-/

namespace oracle_comp

open oracle_comp
open_locale big_operators nnreal ennreal

variables {α β γ ι : Type} {spec spec' : oracle_spec}
  (oa : oracle_comp spec α) (oa' : oracle_comp spec' α)
  (ob : α → oracle_comp spec β) (ob' : α → oracle_comp spec' β)
  (a a' : α) (e e' : set α) (e'' : set β)

section indep_events

/-- Two collections of sets are independent if any two sets have intersection
  of probaility equal to the product of the individual probability.
  Independence is defined using a measure with `measurable_space` `⊤`.
  Further lemmas are written to be independent of this. -/
def indep_events (oa : oracle_comp spec α) (events events' : set (set α)) : Prop :=
@probability_theory.indep_sets α ⊤ events events' (@pmf.to_measure α ⊤ ⁅oa⁆)

variables (events events' : set (set α))

lemma indep_events_iff_indep_sets (oa : oracle_comp spec α) (es es' : set (set α)) :
  indep_events oa es es' ↔ @probability_theory.indep_sets α ⊤ es es' (@pmf.to_measure α ⊤ ⁅oa⁆) :=
iff.rfl

lemma indep_events_iff : indep_events oa events events' ↔
  ∀ e e', e ∈ events → e' ∈ events' → ⁅e ∩ e' | oa⁆ = ⁅e | oa⁆ * ⁅e' | oa⁆ :=
by simp_rw [indep_events_iff_indep_sets, probability_theory.indep_sets,
  prob_event_eq_to_measure_apply]

lemma indep_events_iff_of_eval_dist_eq (h : ⁅oa⁆ = ⁅oa'⁆) :
  oa.indep_events events events' ↔ oa'.indep_events events events' :=
by simp only [indep_events_iff, prob_event, h]

lemma prob_event_inter_eq_mul_of_indep_events (h : indep_events oa events events')
  (he : e ∈ events) (he' : e' ∈ events') : ⁅ e ∩ e' | oa ⁆ = ⁅ e | oa ⁆ * ⁅ e' | oa ⁆ :=
(indep_events_iff oa events events').1 h e e' he he'

end indep_events

section indep_event

/-- To events are independent if the prob of the intersection equals product of individual probs.
  Equivalent to `indep_events` with singleton collections of sets-/
def indep_event (oa : oracle_comp spec α) (e e' : set α) : Prop :=
indep_events oa {e} {e'}

lemma indep_event_iff_indep_events : indep_event oa e e' ↔ indep_events oa {e} {e'} :=
iff.rfl

lemma indep_event_of_indep_events (h : oa.indep_events {e} {e'}) : oa.indep_event e e' :=
(oa.indep_event_iff_indep_events e e').2 h

lemma indep_event_iff_indep_set : indep_event oa e e' ↔
  @probability_theory.indep_set α ⊤ e e' (@pmf.to_measure α ⊤ ⁅oa⁆) :=
by rw [indep_event_iff_indep_events, indep_events_iff_indep_sets,
  probability_theory.indep_set_iff_indep_sets_singleton]; apply measurable_space.measurable_set_top

lemma indep_event_iff : indep_event oa e e' ↔ ⁅e ∩ e' | oa⁆ = ⁅e | oa⁆ * ⁅e' | oa⁆ :=
begin
  simp_rw [indep_event_iff_indep_set, prob_event_eq_to_measure_apply],
  exact probability_theory.indep_set_iff_measure_inter_eq_mul trivial trivial _,
end

lemma indep_event_iff_of_eval_dist_eq (h : ⁅oa⁆ = ⁅oa'⁆) :
  oa.indep_event e e' ↔ oa'.indep_event e e' :=
by simp only [indep_event_iff, prob_event, h]

lemma prob_event_inter_eq_mul_of_indep_event (h : indep_event oa e e') :
  ⁅e ∩ e' | oa⁆ = ⁅e | oa⁆ * ⁅e' | oa⁆ :=
(indep_event_iff oa e e').1 h

end indep_event

lemma indep_events_iff_forall_indep_event (es es' : set (set α)) :
  oa.indep_events es es' ↔ ∀ e ∈ es, ∀ e' ∈ es', oa.indep_event e e' :=
begin
  simp [indep_events_iff, indep_event_iff, imp_forall_iff],
end

end oracle_comp