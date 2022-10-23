import computational_monads.oracle_spec

/-!
# Oracle Query Log

This file efines a simple definition of a log for queries based on continuations.
This definition is chosen over a list of sigma types to give simple type equalities.
-/

/-- Data type representing a log of oracle queries for a given `oracle_spec`.
  Represented as a list of query inputs and outputs, indexed by the indexing set in the spec -/
def query_log (spec : oracle_spec) : Type :=
Π (i : spec.ι), list (spec.domain i × spec.range i)

namespace query_log

open oracle_spec 

@[ext]
lemma ext {spec : oracle_spec} {log log' : query_log spec} (h : ∀ (i : spec.ι), log i = log' i) :
  log = log' := funext h

/-- Empty query log, with no entries for any of the oracles in the spec -/
@[inline, reducible]
def init (spec : oracle_spec) : query_log spec := λ i, []

@[simp]
lemma init_apply (spec : oracle_spec) (i : spec.ι) : (init spec) i = [] := rfl

variables {spec : oracle_spec} (log : query_log spec) [computable spec]

section log_query

/-- Given a current query log, return the new log after adding a given oracle query -/
def log_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) : query_log spec :=
λ j, if hi : i = j then hi.rec_on ((t, u) :: (log i)) else log j

@[simp]
lemma log_query_apply (i j : spec.ι) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u) j = if hi : i = j then hi.rec_on ((t, u) :: log i) else log j := rfl

lemma log_query_apply_of_index_eq {i j : spec.ι} (hi : i = j) (t : spec.domain i)
  (u : spec.range i) : (log.log_query i t u) j = hi.rec_on ((t, u) :: log i) :=
dite_eq_iff.2 (or.inl ⟨hi, rfl⟩)

@[simp]
lemma log_query_apply_same_index (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u) i = (t, u) :: (log i) := log_query_apply_of_index_eq log rfl t u

lemma log_query_apply_of_index_ne {i j : spec.ι} (hi : i ≠ j) (t : spec.domain i)
  (u : spec.range i) : (log.log_query i t u) j = log j := dite_eq_iff.2 (or.inr ⟨hi, rfl⟩)

end log_query

section not_queried

/- Returns whether a specific input has been previously logged -/
def not_queried (i : spec.ι) (t : spec.domain i) : bool :=
((log i).find ((=) t ∘ prod.fst)).is_none

lemma not_queried_def (i : spec.ι) (t : spec.domain i) :
  log.not_queried i t = ((log i).find ((=) t ∘ prod.fst)).is_none := rfl

lemma not_queried_init_eq_tt (i : spec.ι) (t : spec.domain i) :
  (init spec).not_queried i t = tt := rfl

lemma not_queried_log_query (i j : spec.ι) (t : spec.domain i) (t' : spec.domain j)
  (u : spec.range i) : (log.log_query i t u).not_queried j t' =
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
(log.not_queried_log_query i j t t' u).trans ((congr_arg _ (dif_neg hi)).trans (band_tt _))

end not_queried

section map_at_index

/-- Apply a mapping function to the log corresponding to a particular index
  TODO: I think a lot of the above functions can use this as a helper -/
def map_at_index (i : spec.ι)
  (f : list (spec.domain i × spec.range i) → list (spec.domain i × spec.range i)) :
  query_log spec :=
λ j, if hi : i = j then hi.rec_on (f $ log i) else (log j)

variables (i j : spec.ι)
  (f : list (spec.domain i × spec.range i) → list (spec.domain i × spec.range i))

@[simp]
lemma map_at_index_apply : log.map_at_index i f j =
  if hi : i = j then hi.rec_on (f $ log i) else log j := rfl

lemma map_at_index_apply_of_index_eq (h : i = j) : log.map_at_index i f j = h.rec_on (f $ log i) :=
by simp only [h, map_at_index_apply, dif_pos]

lemma map_at_index_apply_same_index : log.map_at_index i f i = f (log i) :=
by simp only [map_at_index_apply, eq_self_iff_true, dite_eq_ite, if_true]

lemma map_at_index_apply_of_index_ne (h : i ≠ j) : log.map_at_index i f j = log j :=
by simp only [h, not_false_iff, map_at_index_apply, dif_neg]

@[simp]
lemma map_at_index_init_of_nil_nil (hf : f [] = []) :
  (init spec).map_at_index i f = init spec :=
begin
  refine ext (λ i, _),
  simp only [hf, map_at_index_apply, init_apply, dite_eq_right_iff],
  exact (λ h, by {induction h, refl})
end

@[simp]
lemma map_at_index_log_query_of_ne (h : i ≠ j) (t : spec.domain j) (u : spec.range j) :
  (log.log_query j t u).map_at_index i f = (log.map_at_index i f).log_query j t u :=
begin
  refine ext (λ k, _),
  by_cases hi : i = k,
  { rw [map_at_index_apply_of_index_eq _ i k f hi],
    by_cases hj : j = k,
    { exact false.elim (h $ hi.trans hj.symm) },
    { rw [log_query_apply_of_index_ne _ hj t u, log_query_apply_of_index_ne _ h.symm t u, 
        map_at_index_apply_of_index_eq log _ _ f hi] } },
  { rw [map_at_index_apply_of_index_ne _ i k f hi],
    by_cases hj : j = k,
    { rw [log_query_apply_of_index_eq log hj t u, log_query_apply_of_index_eq _ hj t u,
        map_at_index_apply_of_index_ne log i j f h] },
    { rw [log_query_apply_of_index_ne log hj t u, log_query_apply_of_index_ne _ hj t u,
        map_at_index_apply_of_index_ne _ i k f hi] } }
end

end map_at_index

section drop_at_index

def drop_at_index (log : query_log spec) (i : spec.ι) (n : ℕ) : query_log spec :=
log.map_at_index i (list.drop n)

variables (n : ℕ)

@[simp]
lemma drop_at_index_apply (i j : spec.ι) :
  (log.drop_at_index i n) j = if i = j then (log j).drop n else log j :=
begin
  simp only [drop_at_index, map_at_index_apply],
  split_ifs,
  { induction h,
    exact rfl },
  { exact rfl }
end

lemma drop_at_index_apply_of_index_eq {i j : spec.ι} (h : i = j) :
  (log.drop_at_index i n) j = (log j).drop n :=
by simp only [h, drop_at_index_apply, eq_self_iff_true, if_true]

@[simp]
lemma drop_at_index_apply_same_index (i : spec.ι) :
  (log.drop_at_index i n) i = (log i).drop n :=
drop_at_index_apply_of_index_eq log n rfl

lemma drop_at_index_apply_of_index_ne {i j : spec.ι} (h : i ≠ j) :
  (log.drop_at_index i n) j = log j :=
by simp only [h, drop_at_index_apply, if_false]

@[simp]
lemma drop_at_index_zero (i : spec.ι) :
  log.drop_at_index i 0 = log :=
ext (λ j, by simp only [list.drop, drop_at_index_apply, if_t_t])

@[simp]
lemma drop_at_index_init (i : spec.ι) :
  (init spec).drop_at_index i n = init spec :=
map_at_index_init_of_nil_nil i (list.drop n) (list.drop_nil n)

@[simp]
lemma drop_at_index_succ_log_query (i j : spec.ι) (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).drop_at_index j (n + 1) = 
    if i = j then log.drop_at_index j n
      else (log.drop_at_index j (n + 1)).log_query i t u :=
begin
  split_ifs,
  { refine ext (λ k, _),
    by_cases hj : j = k,
    { induction h, induction hj,
      simp only [list.drop, drop_at_index_apply_same_index, log_query_apply_same_index] },
    { rw [drop_at_index_apply_of_index_ne _ (n + 1) hj, log_query_apply_of_index_ne log (ne_of_eq_of_ne h hj),
        drop_at_index_apply_of_index_ne _ n hj] } },
  { exact map_at_index_log_query_of_ne log j i _ (ne.symm h) t u }
end

end drop_at_index

section remove_head

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
lemma remove_head_init (i : spec.ι) : (init spec).remove_head i = init spec :=
ext (λ i', if_t_t (i = i') [])

lemma remove_head_log_query (i j : spec.ι)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head j =
    if hi : i = j then log else (log.remove_head j).log_query i t u :=
begin
  split_ifs with hi,
  { induction hi,
    refine (ext $ λ k, trans (remove_head_apply _ i k) _),
    split_ifs with hk,
    { induction hk,
      rw [log_query_apply_same_index log, list.tail_cons] },
    { exact log_query_apply_of_index_ne log hk t u } },
  { refine (ext $ λ k, _),
    simp only [remove_head_apply],
    split_ifs with hj,
    { induction hj,
      simp only [log_query_apply_of_index_ne _ hi, remove_head_apply_same_index] },
    { simp only [log_query_apply, remove_head_apply_of_index_ne _ hj,
        remove_head_apply_of_index_ne _ (ne.symm hi)] } }
end

lemma remove_head_log_query_of_index_eq {i j : spec.ι} (hi : i = j)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head j = log :=
trans (log.remove_head_log_query i j t u) (if_pos hi)

@[simp]
lemma remove_head_log_query_of_same_index (i : spec.ι)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head i = log :=
log.remove_head_log_query_of_index_eq rfl t u

lemma remove_head_log_query_of_index_ne {i j : spec.ι} (hi : i ≠ j)
  (t : spec.domain i) (u : spec.range i) :
  (log.log_query i t u).remove_head j = (log.remove_head j).log_query i t u :=
trans (log.remove_head_log_query i j t u) (if_neg hi)

end remove_head

end query_log
