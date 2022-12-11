/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.query_log.basic

/-!
# Forking Operations for Query Logs

This file defines functions for forking a `query_log`, in the sense of removing
all queries after some specified query, leaving the ones before that as is.
-/

namespace query_log

variables {spec : oracle_spec} (log : query_log spec)

section fork_cache

/-- Remove parts of the cache after the query chosen to fork on.
Just wraps a call to `drop_at_index`, dropping everything if the input is `none`.
The result contains exactly the back `i` elements. The choice to drop everything given a `none`
input is just convention, but simplifies some proofs. -/
def fork_cache (log : query_log spec)
  (i : spec.ι) (n : option ℕ) : query_log spec :=
match n with
| none := query_log.init spec
| (some m) := log.drop_at_index i ((log i).length - m) -- The front values are most recent??
end

@[simp] lemma fork_cache_init (i : spec.ι) (n : option ℕ) :
  (query_log.init spec).fork_cache i n = query_log.init spec :=
begin
  induction n with n,
  { exact rfl },
  { exact drop_at_index_init _ i }
end

@[simp] lemma fork_cache_none (i : spec.ι) (log : query_log spec) :
  log.fork_cache i none = query_log.init spec := rfl

end fork_cache

section to_seed

/-- Wrapping function that just reverses every list in the given `query_log`. 
  Intended to turn a log into something that can be used as a seed for a computation.
  Needed because the logging function adds the new queries to the front of the list  -/
def to_seed (log : query_log spec) :
  query_log spec :=
λ i, (log i).reverse

@[simp]
lemma to_seed_apply (log : query_log spec) (i : spec.ι) :
  log.to_seed i = (log i).reverse :=
rfl

@[simp]
lemma to_seed_init (spec : oracle_spec) :
  (init spec).to_seed = init spec :=
rfl

lemma to_seed_log_query (log : query_log spec)
  (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).to_seed = λ j, if hi : i = j
    then log.to_seed j ++ [hi.rec_on (t, u)] else log.to_seed j :=
begin
  refine ext (λ j, _),
  split_ifs,
  { induction h,
    exact trans (congr_arg list.reverse $ log.log_query_apply_same_index i t u)
      (list.reverse_cons (t, u) (log i)) },
  { exact congr_arg list.reverse (log.log_query_apply_of_index_ne h t u) }
end

end to_seed

end query_log
