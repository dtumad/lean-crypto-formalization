/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count

/-!
# Log for Tracking and Storing Oracle Queries

This file defines a `query_store` structure for tracking oracle outputs during a computation.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

-- TODO: `query_seed`??
@[ext] structure query_store' (spec : oracle_spec) extends query_count spec :=
(get_store : Π (i : spec.ι), list (spec.range i))
(length_get_store_eq_get_count (i : spec.ι) : (get_store i).length = get_count i)

@[ext] structure query_log' (spec : oracle_spec) extends query_count spec :=
(get_log : Π (i : spec.ι), list (spec.domain i × spec.range i))
(length_get_log_eq_get_count (i : spec.ι) : (get_log i).length = get_count i)

lemma mem_active_oracles_iff_ne_nil (qs : query_store' spec) (i) :
  i ∈ qs.active_oracles ↔ qs.get_store i ≠ [] :=
begin
  simp_rw [query_count.mem_active_oracles_iff,
    ne.def, ← list.length_eq_zero, query_store'.length_get_store_eq_get_count
    ],
end

/-- Data type representing a log of oracle queries for a given `oracle_spec`,
represented as a function from oracle indices to lists of query input / output pairs. -/
structure query_store (spec : oracle_spec) : Type :=
(get_store : Π (i : spec.ι), list (spec.range i))
(active_oracles : finset spec.ι)
(mem_active_oracles_iff (i : spec.ι) : i ∈ active_oracles ↔ get_store i ≠ [])

namespace query_store

section empty

/-- Empty store containing no query outputs for any of the oracles. -/
def empty (spec : oracle_spec) : query_store spec :=
{ get_store := λ i, [],
  active_oracles := ∅,
  mem_active_oracles_iff := λ i, (ne_self_iff_false []).symm }

instance : has_emptyc (query_store spec) := ⟨query_store.empty spec⟩
instance : inhabited (query_store spec) := ⟨∅⟩

end empty

section log_query

/-- Add an additional query output to a store of queries. -/
def log_query (store : query_store spec) (i : spec.ι) (u : spec.range i) : query_store spec :=
{ get_store := λ i', if h : i = i' then h.rec_on (u :: store.get_store i) else store.get_store i',
  active_oracles := insert i store.active_oracles,
  mem_active_oracles_iff := begin
    sorry,
  end }

notation `[` u `;` store `]` := log_query store _ u

end log_query

section log_query_list

/-- Add all query outputs in a list to a store of queries. -/
def log_query_list {i} : query_store spec → list (spec.range i) → query_store spec
| store list.nil := store
| store (u :: us) := log_query_list [u; store] us

end log_query_list

section to_query_count

def to_query_count (store : query_store spec) : query_count spec :=
{ get_count := λ i, (store.get_store i).length,
  active_oracles := store.active_oracles,
  mem_active_oracles_iff := λ i, by simp [mem_active_oracles_iff, list.length_eq_zero] }

end to_query_count

end query_store

end oracle_comp
