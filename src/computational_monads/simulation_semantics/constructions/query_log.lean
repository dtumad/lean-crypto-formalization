import computational_monads.oracle_spec

/-- Data type representing a log of oracle queries for a given `oracle_spec`.
  Represented as a list of query inputs and outputs, indexed by the indexing set in the spec -/
def query_log (spec : oracle_spec) : Type :=
  Π (i : spec.ι), list (spec.domain i × spec.range i)

namespace query_log

variables {spec : oracle_spec} (log : query_log spec)

section init

/-- Empty query log, with no entries for any of the oracles in the spec -/
@[inline, reducible]
def init (spec : oracle_spec) : query_log spec :=
λ i, []

@[simp]
lemma init_apply (spec : oracle_spec) (i : spec.ι) :
  (init spec) i = [] :=
rfl

end init

section log_query

variable [spec.computable] 

/-- Given a current query log, return the new log after adding a given oracle query -/
def log_query (log : query_log spec) (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  query_log spec :=
λ j, if hi : i = j then hi.rec_on ((t, u) :: (log i)) else log j

lemma log_query_apply (i j : spec.ι) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u) j = if hi : i = j then hi.rec_on ((t, u) :: log i) else log j :=
rfl

lemma log_query_apply_of_index_eq (log : query_log spec)
  {i j : spec.ι} (hi : i = j) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u) j = hi.rec_on ((t, u) :: log i) :=
dite_eq_iff.2 (or.inl ⟨hi, rfl⟩)

@[simp]
lemma log_query_apply_same_index (log : query_log spec)
  (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u) i = (t, u) :: (log i) :=
log_query_apply_of_index_eq log rfl t u

lemma log_query_apply_of_index_ne (log : query_log spec)
  {i j : spec.ι} (hi : i ≠ j) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u) j = log j :=
dite_eq_iff.2 (or.inr ⟨hi, rfl⟩)

end log_query

section lookup

variable [spec.computable]

/-- Find the query output of the first oracle query with the given input.
  Result is returned as an `option`, with `none` for inputs that haven't previously been queried -/
def lookup (log : query_log spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) :=
((log i).find $ (= t) ∘ prod.fst).map prod.snd

@[simp]
lemma lookup_init (spec : oracle_spec) [spec.computable]
  (i : spec.ι) (t : spec.domain i) :
  (init spec).lookup i t = none :=
option.map_none'

/-- Most general version of the lemma is somewhat cumbersome because of the equality induction.
  More specific versions given below are usually more usefull -/
lemma lookup_log_query (i j : spec.ι)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).lookup j t' = if hi : i = j
    then (if hi.rec_on t = t' then hi.rec_on (some u) else log.lookup j t')
    else log.lookup j t' := 
begin
  split_ifs with hi ht,
  { induction hi, induction ht,
    simp only [lookup, log_query_apply_same_index,
      list.find_cons_of_pos, function.comp_app, option.map_some'] },
  { induction hi,
    refine congr_arg (option.map prod.snd) _,
    refine (log.log_query_apply_same_index i t u).symm ▸ _,
    exact list.find_cons_of_neg (log i) ht },
  { refine congr_arg (option.map prod.snd ∘ _) _,
    exact (log.log_query_apply_of_index_ne hi t u) }
end

@[simp]
lemma lookup_log_query_same_index (i : spec.ι)
  (t t' : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).lookup i t' = if t = t' then some u else log.lookup i t' :=
trans (log.lookup_log_query  i i t t' u) (dif_pos rfl)

lemma lookup_log_query_of_index_ne (i j : spec.ι) (hi : i ≠ j)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).lookup j t' = log.lookup j t' :=
trans (log.lookup_log_query i j t t' u) (dif_neg hi)

@[simp]
lemma lookup_log_query_same_input (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).lookup i t = some u :=
trans (log.lookup_log_query_same_index i t t u) (if_pos rfl)

lemma lookup_log_query_of_input_ne (i : spec.ι)
  (t t' : spec.domain i) (ht : t ≠ t') (u : spec.range i) :
  (log.log_query i t u).lookup i t' = log.lookup i t' :=
trans (log.lookup_log_query_same_index i t t' u) (if_neg ht)

end lookup

section remove_head

variable [spec.computable]

-- remove the head of the index `i` log
def remove_head (log : query_log spec) (i : spec.ι) :
  query_log spec :=
λ j, if i = j then (log j).tail else (log j)

@[simp]
lemma remove_head_apply (i j : spec.ι) :
  log.remove_head i j = if i = j then (log j).tail else (log j) :=
rfl

lemma remove_head_apply_of_index_eq {i j : spec.ι} (hi : i = j) :
  log.remove_head i j = (log j).tail :=
if_pos hi

@[simp]
lemma remove_head_apply_same_index (i : spec.ι) :
  log.remove_head i i = (log i).tail :=
log.remove_head_apply_of_index_eq rfl

lemma remove_head_apply_of_index_ne {i j : spec.ι} (hi : i ≠ j) :
  log.remove_head i j = log j :=
if_neg hi

@[simp]
lemma remove_head_init (spec : oracle_spec) [spec.computable] (i : spec.ι) :
  (init spec).remove_head i = init spec :=
funext (λ i', if_t_t (i = i') [])

lemma remove_head_log_query (i j : spec.ι)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head j =
    if hi : i = j then log else (log.remove_head j).log_query i t u :=
begin
  split_ifs with hi,
  { induction hi,
    refine (funext $ λ k, trans (remove_head_apply _ i k) _),
    split_ifs with hk,
    { induction hk,
      rw [log_query_apply_same_index log, list.tail_cons] },
    { exact log_query_apply_of_index_ne log hk t u } },
  { refine (funext $ λ k, _),
    simp only [remove_head_apply],
    split_ifs with hj,
    { induction hj,
      simp only [log_query_apply_of_index_ne _ hi, remove_head_apply_same_index] },
    { simp only [log_query_apply, remove_head_apply_of_index_ne _ hj,
        remove_head_apply_of_index_ne _ (ne.symm hi)] } }
end

lemma remove_head_log_query_apply_of_index_eq {i j : spec.ι} (hi : i = j)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head j = log :=
trans (log.remove_head_log_query i j t u) (if_pos hi)

@[simp]
lemma remove_head_log_query_apply_of_same_index (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head i = log :=
log.remove_head_log_query_apply_of_index_eq rfl t u

lemma remove_head_log_query_apply_of_index_ne {i j : spec.ι} (hi : i ≠ j)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head j = (log.remove_head j).log_query i t u :=
trans (log.remove_head_log_query i j t u) (if_neg hi)

end remove_head

section not_queried

variable [spec.computable]

-- Check that a input was never queried
def not_queried (log : query_log spec) (i : spec.ι) (t : spec.domain i) : bool :=
((log i).find ((=) t ∘ prod.fst)).is_none

lemma not_queried_def (i : spec.ι) (t : spec.domain i) :
  log.not_queried i t = ((log i).find ((=) t ∘ prod.fst)).is_none :=
rfl

lemma not_queried_init_eq_tt (spec : oracle_spec) [spec.computable]
  (i : spec.ι) (t : spec.domain i) :
  (init spec).not_queried i t = tt :=
rfl

lemma not_queried_log_query (i j : spec.ι)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).not_queried j t' =
    (log.not_queried j t') && (if hi : i = j then (hi.rec_on t ≠ t') else tt) :=
begin
  split_ifs with hi,
  { induction hi,
    rw [not_queried, log_query_apply_same_index],
    by_cases ht : t' = t,
    { induction ht,
      have : (eq t' ∘ prod.fst) (t', u) := (function.comp_app (eq t') prod.fst (t', u)).symm ▸ rfl,
      simp only [list.find_cons_of_pos _ this, option.is_none_some, ne.def, eq_self_iff_true,
        not_true, to_bool_false_eq_ff, band_ff] },
    { have : ¬ (eq t' ∘ prod.fst) (t, u) := by simp only [ht, function.comp_app, not_false_iff],
      simpa only [list.find_cons_of_neg _ this, ht, ne.symm ht,
        ne.def, not_false_iff, to_bool_true_eq_tt, band_tt] } },
  { simp only [not_queried, log_query_apply_of_index_ne log hi, band_tt] }
end

lemma not_queried_log_query_of_index_eq {i j : spec.ι} (hi : i = j)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).not_queried j t' = (log.not_queried j t') && (hi.rec_on t ≠ t') :=
(log.not_queried_log_query i j t t' u).trans (congr_arg ((&&) $ log.not_queried j t') (dif_pos hi))

lemma not_queried_log_query_same_index (i : spec.ι)
  (t t' : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).not_queried i t' = (log.not_queried i t') && (t ≠ t') :=
log.not_queried_log_query_of_index_eq rfl t t' u

lemma not_queried_log_query_of_index_ne {i j : spec.ι} (hi : i ≠ j)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).not_queried j t' = log.not_queried j t' :=
(log.not_queried_log_query i j t t' u).trans 
  ((congr_arg _ (dif_neg hi)).trans (band_tt _))

end not_queried

section to_seed

/-- Wrapping function that just reverses every list in the given `query_log`. 
  Intended to turn a log into something that can be used as a seed for a computation.
  Needed because the logging function adds the new queries to the front  -/
def to_seed (log : query_log spec) :
  query_log spec :=
λ i, (log i).reverse

end to_seed

-- Different lookup that only looks at head, and removes the element from the cache
def take_fst [spec.computable]
  (log : query_log spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) × query_log spec :=
match (log i).nth 0 with
| none := (none, query_log.init spec)
| some ⟨t', u⟩ := if t' = t then (some u, log.remove_head i)
    else (none, query_log.init spec) -- TODO: maybe don't clear everything here?
end

/-- Get the index of the given input, with depth at most equal to the given number `q`.
  In most applications `q` will be the maximum number of queries that a computation makes.
  This allows the result to be bounded and therefore returned as a `fin q` rather than a `ℕ` -/
def get_index [spec.computable] (log : query_log spec)
  (i : spec.ι) (t : spec.domain i) (q : ℕ) : option (fin q) :=
match (log i) with
| [] := none
| ((t', u) :: ls) := sorry
end 

/-- Remove parts of the cache after the query chosen to fork on -/
def fork_cache {q : ℕ} {T U : Type} [inhabited U] : (option $ fin q) → query_log (T →ₒ U) → query_log (T →ₒ U)
:= sorry -- TODO: This is essentially in the `query_log.lean` file but needs a few modifications

end query_log
