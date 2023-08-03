/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.order

/-!
# Log for Tracking and Storing Oracle Queries

This file defines a `query_seed` structure for tracking oracle outputs during a computation.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- Data type representing a seed of oracle query outputs for a given `oracle_spec`,
represented as a function from oracle indices to lists of query outputs,
extending `query_count` such that the count gives the length of the seed. -/
@[ext] structure query_seed (spec : oracle_spec) extends query_count spec :=
(get_seed : Π (i : spec.ι), list (spec.range i))
(get_count_eq_length_get_seed' (i : spec.ι) : get_count i = (get_seed i).length)

/-- View a `query_seed` as a function from oracle index to a count. -/
instance query_seed.fun_like (spec : oracle_spec) :
  fun_like (query_seed spec) spec.ι (λ i, list (spec.range i)) :=
{ coe := query_seed.get_seed,
  coe_injective' := λ qs qs' h, query_seed.ext qs qs' (fun_like.ext _ _
    (by simp only [← query_count.get_count_eq_apply, query_seed.get_count_eq_length_get_seed',
      h, eq_self_iff_true, imp_true_iff])) h }

namespace query_seed

variables (qs qs' qs'' : query_seed spec)

@[simp] lemma get_seed_eq_apply (i) : qs.get_seed i = qs i := rfl

lemma to_query_count_apply_eq_length (i) : qs.to_query_count i = (qs i).length :=
get_count_eq_length_get_seed' qs i

@[simp] lemma length_apply_eq_to_query_count_apply (i) : (qs i).length = qs.to_query_count i :=
(get_count_eq_length_get_seed' qs i).symm

lemma mem_active_oracles_iff (qs : query_seed spec) (i) : i ∈ qs.active_oracles ↔ qs i ≠ [] :=
by rw [query_count.mem_active_oracles_iff, to_query_count_apply_eq_length,
  ne.def, ne.def, list.length_eq_zero]

@[simp] lemma apply_eq_nil_iff (i) : qs i = [] ↔ i ∉ qs.active_oracles :=
by simp [mem_active_oracles_iff]

@[simp] lemma length_apply_eq_zero_iff (i) : (qs i).length = 0 ↔ i ∉ qs.active_oracles :=
by simp [list.length_eq_zero]

lemma to_query_count_apply_eq_zero_iff (i) : qs.to_query_count i = 0 ↔ i ∉ qs.active_oracles :=
(query_count.apply_eq_zero_iff _ _)

section empty

/-- Empty seed containing no query outputs for any of the oracles. -/
protected def empty (spec : oracle_spec) : query_seed spec :=
{ get_seed := λ i, [],
  to_query_count := ∅,
  get_count_eq_length_get_seed' := λ i, rfl }

instance : has_emptyc (query_seed spec) := ⟨query_seed.empty spec⟩
instance : inhabited (query_seed spec) := ⟨∅⟩

@[simp] lemma empty_apply (i) : (∅ : query_seed spec) i = [] := rfl

@[simp] lemma to_query_count_empty : (∅ : query_seed spec).to_query_count = ∅ := rfl

lemma active_oracles_empty : (∅ : query_seed spec).active_oracles = ∅ := rfl

lemma not_mem_active_oracles_empty (i) : i ∉ (∅ : query_seed spec).active_oracles := by simp

lemma to_query_count_eq_empty_iff : qs.to_query_count = ∅ ↔ qs = ∅ :=
by simp [fun_like.ext_iff]

end empty

section of_list

/-- Generate a seed from a list of query outputs for a single oracle,
leaving the seed empty for any of the other oracles. -/
def of_list {i} (us : list (spec.range i)) : query_seed spec :=
{ get_seed := λ i', if h : i = i' then h.rec_on us else [],
  to_query_count := query_count.of_nat i us.length,
  get_count_eq_length_get_seed' := λ i', begin
    by_cases hi : i = i',
    { induction hi, simp },
    { simp [hi] }
  end }

variables {i : spec.ι} (us us' : list (spec.range i))

@[simp] lemma of_list_apply (i') : (of_list us) i' = if h : i = i' then h.rec_on us else [] := rfl

@[simp] lemma to_query_count_of_list : (of_list us).to_query_count =
  query_count.of_nat i us.length := rfl

lemma to_query_count_of_list_apply (i') :
  (of_list us).to_query_count i' = if i = i' then us.length else 0 :=
by rw [to_query_count_of_list, query_count.of_nat_apply]

lemma active_oracles_of_list :
  (of_list us).active_oracles = if us = [] then ∅ else {i} :=
by simp [to_query_count_of_list, query_count.active_oracles_of_nat, list.length_eq_zero]

@[simp] lemma of_list_nil : of_list ([] : list (spec.range i)) = ∅ :=
by rw [← to_query_count_eq_empty_iff, to_query_count_of_list, list.length, query_count.of_nat_zero]

end of_list

section append

/-- Combine two seeds by individually appending the seed for each oracle. -/
protected def append (qs qs' : query_seed spec) : query_seed spec :=
{ get_seed := λ i, qs i ++ qs' i,
  to_query_count := qs.to_query_count + qs'.to_query_count,
  get_count_eq_length_get_seed' := by simp }

instance (spec : oracle_spec) : has_append (query_seed spec) :=
{ append := query_seed.append }

@[simp] lemma append_apply (i) : (qs ++ qs') i = qs i ++ qs' i := rfl

@[simp] lemma to_query_count_append : (qs ++ qs').to_query_count =
  qs.to_query_count + qs'.to_query_count := rfl

lemma to_query_count_append_apply (i) : (qs ++ qs').to_query_count i =
  qs.to_query_count i + qs'.to_query_count i := rfl

lemma active_oracles_append : (qs ++ qs').active_oracles =
  qs.active_oracles ∪ qs'.active_oracles := rfl

@[simp] lemma append_empty : qs ++ ∅ = qs := fun_like.ext _ _ (λ i, list.append_nil _)

@[simp] lemma empty_append : ∅ ++ qs = qs := fun_like.ext _ _ (λ i, list.nil_append _)

@[simp] lemma append_assoc : qs ++ qs' ++ qs'' = qs ++ (qs' ++ qs'') :=
fun_like.ext _ _ (λ i, list.append_assoc _ _ _)

end append

section seed_queries

/-- Add a list of query outputs to the seed, appending them to the back of the existing seed. -/
def seed_queries (qs : query_seed spec) {i} (us : list (spec.range i)) : query_seed spec :=
qs ++ of_list us

variables {i : spec.ι} (us us' : list (spec.range i))

@[simp] lemma seed_queries_apply (i') : (qs.seed_queries us) i' =
  if h : i = i' then h.rec_on (qs i ++ us) else qs i' :=
begin
  by_cases hi : i = i',
  { induction hi,
    simp [seed_queries, append_apply, of_list_apply] },
  { simp [seed_queries, append_apply, of_list_apply, hi] }
end

@[simp] lemma to_query_count_seed_queries : (qs.seed_queries us).to_query_count =
  qs.to_query_count.increment i us.length :=
by rw [seed_queries, to_query_count_append, to_query_count_of_list, query_count.add_of_nat]

lemma to_query_count_seed_queries_apply (i') : (qs.seed_queries us).to_query_count i' =
  if h : i = i' then qs.to_query_count i' + us.length else qs.to_query_count i' :=
by simp

@[simp] lemma active_oracles_seed_queries : (qs.seed_queries us).active_oracles =
  if us = [] then qs.active_oracles else insert i qs.active_oracles :=
by simp [query_count.active_oracles_increment, list.length_eq_zero]

@[simp] lemma seed_queries_nil : (qs.seed_queries ([] : list (spec.range i))) = qs :=
fun_like.ext _ _ (λ i, by rw [seed_queries, of_list_nil, append_empty])

end seed_queries

section seed_query

/-- Add a single query output to the seed at the back of the existing seed. -/
def seed_query (qs : query_seed spec) {i} (u : spec.range i) : query_seed spec :=
qs.seed_queries [u]

variables {i : spec.ι} (u u' : spec.range i)

@[simp] lemma seed_query_apply (i') : (qs.seed_query u) i' =
  if h : i = i' then h.rec_on (qs i ++ [u]) else qs i' :=
seed_queries_apply qs [u] i'

@[simp] lemma to_query_count_seed_query : (qs.seed_query u).to_query_count =
  qs.to_query_count.increment i 1 := by simp [seed_query]

lemma to_query_count_seed_query_apply (i') : (qs.seed_query u).to_query_count i' =
  if h : i = i' then qs.to_query_count i' + 1 else qs.to_query_count i' :=
to_query_count_seed_queries_apply qs [u] i'

lemma active_oracles_seed_query : (qs.seed_query u).active_oracles =
  insert i qs.active_oracles := by simp

end seed_query

section take_queries

def take_queries (qs : query_seed spec) (i : spec.ι) (n : ℕ) : query_seed spec :=
{ get_seed := λ i', if i = i' then (qs i').take n else qs i',
  to_query_count := qs.to_query_count.reset_count i n,
  get_count_eq_length_get_seed' := λ i', by by_cases hi : i = i'; simp [hi] }

variables (i : spec.ι) (n m : ℕ)

@[simp] lemma take_queries_apply (i') : (qs.take_queries i n) i' =
  if i = i' then (qs i').take n else qs i' := rfl

@[simp] lemma to_query_count_take_queries : (qs.take_queries i n).to_query_count =
  qs.to_query_count.reset_count i n := rfl

lemma to_query_count_take_queries_apply (i') : (qs.take_queries i n).to_query_count i' =
  if i = i' then min n (qs.to_query_count i') else qs.to_query_count i' := by simp

lemma active_oracles_take_queries : (qs.take_queries i n).active_oracles =
  if n = 0 then qs.active_oracles.erase i else qs.active_oracles := by simp

end take_queries

section drop_queries

def drop_queries (qs : query_seed spec) (i : spec.ι) (n : ℕ) : query_seed spec :=
{ get_seed := λ i', if i = i' then (qs i').drop n else qs i',
  to_query_count := qs.to_query_count.decrement i n,
  get_count_eq_length_get_seed' := λ i', by by_cases h : i = i'; simp [h] }

@[simp] lemma drop_queries_apply (i n i') : (qs.drop_queries i n) i' =
  if i = i' then (qs i').drop n else qs i' := rfl

@[simp] lemma to_query_count_drop_queries (i n) : (qs.drop_queries i n).to_query_count =
  qs.to_query_count.decrement i n := rfl

lemma to_query_count_drop_queries_apply (i n i') : (qs.drop_queries i n).to_query_count i' =
  if i = i' then qs.to_query_count i' - n else qs.to_query_count i' := by simp

lemma active_oracles_drop_queries (i n) : (qs.drop_queries i n).active_oracles =
  if qs.to_query_count i ≤ n then qs.active_oracles.erase i else qs.active_oracles :=
by simp [query_count.active_oracles_decrement]

end drop_queries

end query_seed

end oracle_comp
