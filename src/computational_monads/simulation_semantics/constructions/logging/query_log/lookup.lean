/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging.query_log.basic

/-!
# Lookup Functions for Query Logs

This file defines functions for looking up values in a `query_log`.
-/

namespace query_log

variables {spec : oracle_spec} (log : query_log spec)
variable [spec.computable]

section lookup

/-- Find the query output of the first oracle query with the given input.
  Result is returned as an `option`, with `none` for inputs that haven't previously been queried.
  Main use case is for using the log as a cache for repeated queries.
  Note that this returns the *most recently* logged query, not the first -/
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
    then (if hi.rec_on t = t' then hi.rec_on (some u) else log.lookup j t') else log.lookup j t' := 
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

lemma lookup_eq_none_iff_not_queried (i : spec.ι) (t : spec.domain i) :
  log.lookup i t = none ↔ log.not_queried i t :=
begin
  rw [lookup, option.map_eq_none', list.find_eq_none, not_queried_iff_not_mem],
  exact ⟨λ h u htu, h (t, u) htu rfl, λ h x hu' ht', h x.2 (ht' ▸ (by rwa prod.mk.eta))⟩,
end

lemma exists_eq_lookup_iff_not_not_queried (i : spec.ι) (t : spec.domain i) :
  (∃ (u : spec.range i), some u = log.lookup i t) ↔ ¬ log.not_queried i t :=
by rw [← lookup_eq_none_iff_not_queried, ← ne.def, option.ne_none_iff_exists]

lemma exists_eq_lookup_of_not_not_queried (i : spec.ι) (t : spec.domain i)
  (h : ¬ log.not_queried i t) : ∃ (u : spec.range i), some u = log.lookup i t :=
(exists_eq_lookup_iff_not_not_queried log i t).2 h

end lookup

section lookup_fst

/-- `lookup`, but only checking the front element of the list.
  Main use case is using the `query_log` as a seed for a second computation -/
def lookup_fst (log : query_log spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) :=
match log i with
| [] := none
| ((t', u)) :: _ := if t = t' then some u else none
end

lemma lookup_fst_init (spec : oracle_spec) [spec.computable]
  (i : spec.ι) (t : spec.domain i) :
  (query_log.init spec).lookup_fst i t = none :=
rfl

lemma lookup_fst_log_query (i j : spec.ι)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).lookup_fst j t' = if hi : i = j
    then (if hi.rec_on t = t' then hi.rec_on (some u) else none) else log.lookup_fst j t' :=
begin
  split_ifs with hi ht,
  { induction hi, induction ht,
    simp only [lookup_fst, log_query_apply_same_index, eq_self_iff_true, if_true] },
  { induction hi,
    simpa [lookup_fst] using ne.symm ht },
  { simp only [lookup_fst, log_query_apply_of_index_ne _ hi] }
end

lemma lookup_fst_log_query_of_index_eq {i j : spec.ι} (hi : i = j)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).lookup_fst j t' =
    if hi.rec_on t = t' then hi.rec_on (some u) else none :=
(log.lookup_fst_log_query i j t t' u).trans (dif_pos hi)

lemma lookup_fst_log_query_same_index (i : spec.ι)
  (t t' : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).lookup_fst i t' =
    if t = t' then some u else none :=
log.lookup_fst_log_query_of_index_eq rfl t t' u

lemma lookup_fst_log_query_of_index_ne {i j : spec.ι} (hi : i ≠ j)
  (t : spec.domain i) (t' : spec.domain j) (u : spec.range i) :
  (log.log_query i t u).lookup_fst j t' = log.lookup_fst j t' :=
(log.lookup_fst_log_query i j t t' u).trans (dif_neg hi)

end lookup_fst

section get_index_of_input

/-- Get the index of the first query with the given input `t`.
  Returns `none` if the input has never been queried
  TODO: check if the fold should be right or left-/
def get_index_of_input [spec.computable] (log : query_log spec)
  (i : spec.ι) (t : spec.domain i) : option ℕ :=
(log i).foldr_with_index (λ n ⟨t', _⟩ m, if t' = t then some n else m) none

end get_index_of_input

section update_result_at_index

section update_query_result

/-- Update the result of the first query to `t` to a new value.
If the value was never queried then return the original log. -/
def update_result_at_index [spec.computable] (log : query_log spec) (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) : query_log spec :=
match log.get_index_of_input i t with
| none := log
| (some n) := log.map_at_index i (λ l, l.update_nth n (t, u))
end

end update_query_result


end update_result_at_index

section query_input_same_at

def query_input_same_at (cache cache' : query_log spec)
  (i : spec.ι) (n : ℕ) : Prop :=
match (cache i).reverse.nth n with
| none := true -- An out of bounds will match with anything by convention
| (some ⟨t, u⟩) := some t = ((cache i).reverse.nth n).map prod.fst
end

end query_input_same_at

section query_input_diff_at

-- query_results are different for the two caches at `n`
def query_output_diff_at (cache cache' : query_log spec)
  (i : spec.ι) (n : ℕ) : Prop :=
match (cache i).reverse.nth n with
| none := true -- An out of bounds will differ from anything by convention
| (some ⟨t, u⟩) := some u ≠ ((cache' i).reverse.nth n).map prod.snd
end

end query_input_diff_at

end query_log