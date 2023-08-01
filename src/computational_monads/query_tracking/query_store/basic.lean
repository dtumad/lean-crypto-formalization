/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec

/-!
# Log for Tracking and Storing Oracle Queries

This file defines a `query_store` structure for tracking oracle outputs during a computation.
-/

/-- Data type representing a log of oracle queries for a given `oracle_spec`,
represented as a function from oracle indices to lists of query input / output pairs. -/
def query_store (spec : oracle_spec) : Type :=
Π (i : spec.ι), list (spec.range i)

namespace query_store

open oracle_spec

variables {spec : oracle_spec}

section empty

/-- Empty log containing no queries for any of the oracles. -/
def empty (spec : oracle_spec) : query_store spec := λ i, []

instance (spec : oracle_spec) : has_emptyc (query_store spec) :=
⟨query_store.empty spec⟩

end empty

section log_query

def log_query (store : query_store spec) (i : spec.ι) (u : spec.range i) :
  query_store spec :=
λ i', if h : i = i' then h.rec_on (u :: store i) else store i'

notation `[` u `;` store `]` := log_query store _ u

end log_query

end query_store
