/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec
import computational_monads.query_tracking.query_count.order
import computational_monads.query_tracking.query_seed.basic

/-!
# Oracle Query Log

This file defines a log for tracking oracle queries, represented by a list of input output pairs.
The lists are indexed by a dependent function of oracle indices, and modifications to a log
are implemented using continuation passing of previous logs (viewed as functions).

This definition is chosen over a list of sigma types to give simple type equalities.

-- TODO: use indexed list
-/

namespace oracle_spec

/-- Data type representing a log of oracle queries for a given `oracle_spec`.
  Represented as a list of query inputs and outputs, indexed by the indexing set in the spec -/
@[inline, reducible] def query_log (spec : oracle_spec) : Type :=
spec.indexed_list (λ i, spec.domain i × spec.range i)

namespace query_log

open oracle_spec

variables {spec spec' : oracle_spec}

section log_query

/-- Log a query by adding the input and output values to the log.
Values are added to the back of the current list, so oldest queries come first in the log. -/
def log_query (log : query_log spec) (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  query_log spec := log.add_values [(t, u)]

variables (log : query_log spec) (i : spec.ι) (t : spec.domain i) (u : spec.range i)

@[simp] lemma active_oracles_log_query : (log.log_query i t u).active_oracles =
  insert i log.active_oracles := by simp [log_query]

@[simp] lemma log_query_apply (i' : spec.ι) : (log.log_query i t u) i' =
  if h : i = i' then h.rec_on (log i ++ [(t, u)]) else log i' := by simp [log_query]

@[simp] lemma get_count_log_query (i' : spec.ι) : (log.log_query i t u).get_count i' =
  log.get_count i' + if i = i' then 1 else 0 := by simp [log_query]

@[simp] lemma log_query_ne_empty : log.log_query i t u ≠ ∅ :=
(mt (log.log_query i t u).eq_empty_iff.1) (by simp)

@[simp] lemma to_query_count_log_query : (log.log_query i t u).to_query_count =
  log.to_query_count.increment i 1 := by simp [log_query]

@[simp] lemma le_log_query_self : log ≤ log.log_query i t u := by simp [log_query]

end log_query

section to_seed

def to_seed (log : spec.query_log) : spec.query_seed := log.map (λ _, prod.snd)

end to_seed

section was_queried

@[derive decidable] def was_queried (log : spec.query_log) (i : spec.ι) (t : spec.domain i) :=
(log i).find (((=) t) ∘ prod.fst) = none

end was_queried

end query_log

end oracle_spec
