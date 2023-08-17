/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.indexed_list.order
import computational_monads.distribution_semantics.tactics.push_map_dist_equiv
import computational_monads.distribution_semantics.ite

/-!
# Generate an Indexed List by Running a Computation According to a Count

This file defines a function `generate` for running a computation multiple times based
on a given `query_count`, generating an indexed list of the output types.
Any result will have the same "shape" as the original count, in the sense that it coerces
back to the original count under `indexed_list.coe_query_count`.
-/

namespace oracle_spec

open_locale big_operators
open oracle_comp

namespace indexed_list

variables {α β γ : Type} {spec spec' : oracle_spec} {τ τ' : spec.ι → Type}

/-- Get the first value from an `indexed_list` at an index, and remove it from the list.
If the list at that index is empty, instead run the computation `oa` and return the result. -/
def get_or_else (il : spec.indexed_list τ) (i : spec.ι) [inhabited (τ i)]
  (oa : oracle_comp spec' (τ i)) : oracle_comp spec' (τ i × spec.indexed_list τ) :=
if i ∈ il.active_oracles then return ((il i).head, il.drop_at_index i 1) else (λ t, (t, il)) <$> oa

variables (il il' : spec.indexed_list τ) (i : spec.ι) (oa : oracle_comp spec' (τ i))
variable [inhabited (τ i)]

@[simp] lemma get_or_else_of_mem_active_oracles (hi : i ∈ il.active_oracles) :
  il.get_or_else i oa = return ((il i).head, il.drop_at_index i 1) := if_pos hi

@[simp] lemma get_or_else_of_not_mem_active_oracles (hi : i ∉ il.active_oracles) :
  il.get_or_else i oa = (λ t, (t, il)) <$> oa := if_neg hi

lemma get_or_else_eq_map_iff (f : τ i → τ i × spec.indexed_list τ)
  (oa' : oracle_comp spec' (τ i)) :
  il.get_or_else i oa = f <$> oa' ↔ ∀ t, f t = (t, il) ∧ oa = oa' :=
begin
  by_cases hi : i ∈ il.active_oracles,
  {
    simp [hi],
    sorry,
  },
  {
    sorry
  }
end

lemma get_or_else_of_eq_nil (h : il i = []) : il.get_or_else i oa = (λ t, (t, il)) <$> oa :=
by simp [get_or_else, il.not_mem_active_oracles h]

lemma get_or_else_of_eq_cons (t ts) (h : il i = t :: ts) : il.get_or_else i oa =
  return (t, il.drop_at_index i 1) := by simp [get_or_else, h, il.mem_active_oracles' h]

@[simp_dist_equiv] lemma get_or_else_dist_equiv : il.get_or_else i oa ≃ₚ
  if i ∈ il.active_oracles then return ((il i).head, il.drop_at_index i 1) else (λ t, (t, il)) <$> oa :=
begin
  -- by_cases hi :
  simp [get_or_else],
end

lemma support_get_or_else : (il.get_or_else i oa).support =
  if i ∈ il.active_oracles then {((il i).head, il.drop_at_index i 1)} else {(x, il) | x ∈ oa.support} :=
sorry -- by simp only [get_or_else, set.image, apply_empty_iff]



@[simp] lemma get_or_else_empty : (∅ : spec.indexed_list τ).get_or_else i oa =
  (λ t, (t, ∅)) <$> oa := by simp [get_or_else]

@[simp_dist_equiv] lemma get_or_else_add_dist_equiv [inhabited (τ i)] :
  (il + il').get_or_else i oa ≃ₚ if (il i).empty then prod.map id ((+) il) <$> il'.get_or_else i oa
    else return ((il i).head, il.drop_at_index i 1 + il') :=
begin
  sorry,
  -- simp only [get_or_else, add_apply, drop_at_index_add, apply_empty_iff, ite_not],
  -- by_cases hi : i ∈ il.active_oracles,
  -- { have : ¬ (il i ++ il' i).empty := by simp only [list.empty_iff_eq_nil, hi, list.append_eq_nil,
  --     apply_eq_nil_iff, not_true, false_and, not_false_iff],
  --   simp only [hi, this, nat.sub_eq_zero_of_le (il.one_le_get_count hi), list.head_append, ne.def,
  --     apply_eq_nil_iff, not_true, not_false_iff, drop_at_index_zero, if_false, if_true] },
  -- { by_cases hi' : i ∈ il'.active_oracles,
  --   { have : ¬ (il i ++ il' i).empty := by simp only [list.empty_iff_eq_nil, hi',
  --       list.append_eq_nil, apply_eq_nil_iff, not_true, and_false, not_false_iff],
  --     have hil : il i = [] := apply_eq_nil _ hi,
  --     simp only [hi', hi, hil, get_count_eq_zero _ hi, list.nil_append, apply_empty_iff, not_true,
  --       tsub_zero, if_false, if_true],
  --     refine trans _ (map_return_dist_equiv _ _).symm,
  --     simp only [drop_at_index_eq_self _ _ hi, prod.map_mk, id.def] },
  --   { have : (il i ++ il' i).empty := by simp only [list.empty_iff_eq_nil, hi, hi',
  --       list.append_eq_nil, apply_eq_nil_iff, not_false_iff, and_self],
  --     simp only [this, hi, hi', if_true, if_false],
  --     pairwise_dist_equiv } }
end

@[simp_dist_equiv] lemma get_or_else_of_list_dist_equiv [inhabited (τ i)] (ts : list (τ i)) :
  (of_list ts).get_or_else i oa ≃ₚ if ts.empty then (λ t, (t, ∅)) <$> oa
    else return (ts.head, of_list (ts.tail)) :=
begin
  induction ts,
  { simp },
  { rw [of_list_cons],
    simp only [list.empty, coe_sort_ff, list.head_cons, list.tail_cons, if_false],
    refine trans (get_or_else_add_dist_equiv _ _ _ _) (by simp) }
end

@[simp_dist_equiv] lemma get_or_else_add_values_dist_equiv [inhabited (τ i)] (ts : list (τ i)) :
  (il.add_values ts).get_or_else i oa ≃ₚ if (il i).empty then (if ts.empty
    then (λ t, (t, il)) <$> oa else return (ts.head, il.add_values ts.tail))
      else return ((il i).head, (il.drop_at_index i 1).add_values ts) :=
begin
  -- TODO: this should be more tactic-able
  refine trans (get_or_else_add_dist_equiv _ _ _ _) _,
  by_cases hil : il i = []; cases ts with t ts; simp [list.empty_iff_eq_nil, hil],
  { refine trans (map_comp_dist_equiv _ _ _) _,
    pairwise_dist_equiv,
    simp only [function.comp_app, prod.map_mk, id.def, add_empty] },
  { simp [get_or_else_of_eq_cons _ _ _ t ts (of_list_apply_same_index _),
      dist_equiv_return_iff, set.ext_iff, add_values] },
  { refl },
end

@[simp_dist_equiv] lemma get_or_else_add_values_fresh_dist_equiv [inhabited (τ i)]
  (ts : list (τ i)) (hi : i ∉ il.active_oracles) (hts : ts ≠ []) :
  (il.add_values ts).get_or_else i oa ≃ₚ return' !spec'! (ts.head, il.add_values ts.tail) :=
begin
  refine trans (by apply get_or_else_add_values_dist_equiv) _,
  simp [list.empty_iff_eq_nil, apply_eq_nil il hi, hts],
end

end indexed_list

end oracle_spec