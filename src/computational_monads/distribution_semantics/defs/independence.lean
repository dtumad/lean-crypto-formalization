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

TODO: The theory in this file is kind of lacking still
-/

namespace oracle_comp

open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

section indep_events

/-- Two collections of sets are independent if any two sets have intersection
of probaility equal to the product of the individual probability.
Independence is defined using a measure with `measurable_space` `⊤`.
Further lemmas are written to be independent of this. -/
def indep_events (oa : oracle_comp spec α) (es es' : set (α → Prop)) : Prop :=
@probability_theory.indep_sets α ⊤ es es' (@pmf.to_measure α ⊤ ⁅oa⁆)

lemma indep_events_iff_indep_sets (oa : oracle_comp spec α) (es es' : set (α → Prop)) :
  indep_events oa es es' ↔ @probability_theory.indep_sets α ⊤ es es' (@pmf.to_measure α ⊤ ⁅oa⁆) :=
iff.rfl

lemma indep_events_iff (oa : oracle_comp spec α) (es es' : set (α → Prop)) :
  indep_events oa es es' ↔ ∀ p q : α → Prop, p ∈ es → q ∈ es' →
    ⁅λ x, p x ∧ q x | oa⁆ = ⁅p | oa⁆ * ⁅q | oa⁆ :=
by simpa only [indep_events_iff_indep_sets, probability_theory.indep_sets,
  prob_event_eq_to_measure_apply]

lemma indep_events.prob_event_eq_mul' {oa : oracle_comp spec α} {es es' : set (α → Prop)}
  (h : indep_events oa es es') {p q : α → Prop} (hp : p ∈ es) (hq : q ∈ es') :
  ⁅λ x, p x ∧ q x | oa ⁆ = ⁅p | oa ⁆ * ⁅q | oa⁆ :=
(indep_events_iff oa es es').1 h p q hp hq

end indep_events

section indep_event

/-- To events are independent if the prob of the intersection equals product of individual probs.
  Equivalent to `indep_events` with singleton collections of sets-/
def indep_event (oa : oracle_comp spec α) (p q : α → Prop) : Prop :=
indep_events oa {p} {q}

lemma indep_event_iff_indep_set (oa : oracle_comp spec α) (p q : α → Prop) :
  indep_event oa p q ↔ @probability_theory.indep_set α ⊤ p q (@pmf.to_measure α ⊤ ⁅oa⁆) :=
by simp only [indep_event, indep_events_iff_indep_sets, measurable_space.measurable_set_top,
  probability_theory.indep_set_iff_indep_sets_singleton]

lemma indep_event_iff (oa : oracle_comp spec α) (p q : α → Prop) :
  indep_event oa p q ↔ ⁅λ x, p x ∧ q x | oa⁆ = ⁅p | oa⁆ * ⁅q | oa⁆ :=
begin
  simp_rw [indep_event_iff_indep_set, prob_event_eq_to_measure_apply],
  exact probability_theory.indep_set_iff_measure_inter_eq_mul trivial trivial _,
end

lemma indep_event.prob_event_eq_mul {oa : oracle_comp spec α} {p q : α → Prop}
  (h : indep_event oa p q) : ⁅λ x, p x ∧ q x | oa⁆ = ⁅p | oa⁆ * ⁅q | oa⁆ :=
h.prob_event_eq_mul' rfl rfl

end indep_event

lemma indep_events_iff_forall_indep_event (oa : oracle_comp spec α) (es es' : set (α → Prop)) :
  oa.indep_events es es' ↔ ∀ e ∈ es, ∀ e' ∈ es', oa.indep_event e e' :=
by simp only [indep_events_iff, indep_event_iff, imp_forall_iff]

end oracle_comp