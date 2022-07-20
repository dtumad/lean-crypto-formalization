import computational_monads.simulation_semantics.constructions.logging.query_log.basic

namespace query_log

variables {spec : oracle_spec} (log : query_log spec)

section fork_cache

/-- Remove parts of the cache after the query chosen to fork on.
  Just wraps a call to `drop_at_index`, dropping nothing if the input is `none` -/
def fork_cache [spec.computable] (log : query_log spec)
  (i : spec.ι) (n : option ℕ) : query_log spec :=
match n with
| none := query_log.init spec -- TODO: this case doesn't really matter but whatever
| (some m) := log.drop_at_index i m
end

variable [spec.computable]

lemma fork_cache_init (i : spec.ι) (n : option ℕ) :
  (query_log.init spec).fork_cache i n = query_log.init spec :=
begin
  induction n with n,
  { exact rfl },
  { exact drop_at_index_init n i }
end

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

lemma to_seed_log_query [spec.computable] (log : query_log spec)
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
