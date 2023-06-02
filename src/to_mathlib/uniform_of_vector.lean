/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import probability.probability_mass_function.uniform
import algebra.big_operators.fin

/-!
# Uniform constructions on pmf
-/

variables {α β : Type}

open_locale classical big_operators nnreal ennreal

namespace pmf

section uniform_of_list

noncomputable def uniform_of_list (l : list α) (h : ¬ l.empty) : pmf α :=
pmf.of_multiset (quotient.mk l) (λ hl, h ((multiset.coe_eq_zero_iff_empty l).1 hl))

variables (l : list α) (h : ¬ l.empty)

@[simp] lemma support_uniform_of_list : (uniform_of_list l h).support = {x | x ∈ l} :=
trans (pmf.support_of_multiset _) (set.ext $ λ x, by simp only [multiset.quot_mk_to_coe,
  finset.mem_coe, multiset.mem_to_finset, multiset.mem_coe, set.mem_set_of_eq])

lemma mem_support_uniform_of_list_iff (a : α) : a ∈ (uniform_of_list l h).support ↔ a ∈ l :=
by simp only [support_uniform_of_list, set.mem_set_of_eq]

@[simp] lemma uniform_of_list_apply (a : α) : uniform_of_list l h a = l.count a / l.length :=
by rw [uniform_of_list, pmf.of_multiset_apply, multiset.quot_mk_to_coe,
  multiset.coe_count, multiset.coe_card]

lemma uniform_of_list_apply_of_not_mem (a : α) (ha : a ∉ l) : uniform_of_list l h a = 0 :=
(pmf.apply_eq_zero_iff _ a).2 (mt (mem_support_uniform_of_list_iff l h a).1 ha)

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_uniform_of_list_apply :
  (uniform_of_list l h).to_outer_measure t = l.countp (∈ t) / l.length :=
begin
  suffices : ∑ x in l.to_finset, (l.filter (∈ t)).count x =
    ∑ x in (l.to_finset.filter (∈ t)), l.count x,
  { simp only [uniform_of_list, to_outer_measure_of_multiset_apply, list.length,
      multiset.quot_mk_to_coe, multiset.coe_filter, multiset.coe_count, multiset.coe_card,
      ← finset.sum_filter_count_eq_countp, ← this, nat.cast_sum],
    refine congr_arg (λ x, x / (l.length : ℝ≥0∞)) (tsum_eq_sum (λ x hx, _)),
    simp [(λ h, hx (list.mem_to_finset.2 h) : x ∉ l)] },
  rw [finset.sum_filter],
  refine finset.sum_congr rfl (λ x hx, by split_ifs with hxt; simp [hxt]),
end

@[simp] lemma to_measure_uniform_of_list_apply [measurable_space α] (ht : measurable_set t) :
  (uniform_of_list l h).to_measure t = l.countp t / l.length :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_list_apply l h t)

end measure

end uniform_of_list

section uniform_of_vector

noncomputable def uniform_of_vector {n : ℕ} (v : vector α (n + 1)) : pmf α :=
uniform_of_list v.1 (vector.not_empty_to_list v)

variables {n : ℕ} (v : vector α (n + 1))

@[simp]
lemma support_uniform_of_vector : (uniform_of_vector v).support = {x | x ∈ v.to_list} :=
support_uniform_of_list v.1 (vector.not_empty_to_list v)

@[simp]
lemma uniform_of_vector_apply (a : α) : uniform_of_vector v a = v.to_list.count a / ↑(n + 1) :=
(uniform_of_list_apply v.1 _ a).trans (congr_arg (λ x, _ / x) (congr_arg coe v.length_coe))

lemma uniform_of_vector_eq_nth_map_uniform_of_fintype :
  uniform_of_vector v = pmf.map v.nth (uniform_of_fintype $ fin (n + 1)) :=
pmf.ext (λ x, by calc uniform_of_vector v x
  = v.to_list.count x / n.succ : uniform_of_vector_apply v x
  ... = ↑(∑ i, ite (x = v.nth i) 1 0) / n.succ :
    by rw [← fin.card_filter_univ_eq_vector_nth_eq_count,
      finset.card_eq_sum_ones, finset.sum_filter]
  ... = (∑ i, ite (x = v.nth i) 1 0) / n.succ : by simp only [finset.sum_boole, nat.cast_id]
  ... = (∑' i, ite (x = v.nth i) 1 0) / n.succ :
    congr_arg (λ z, z / (n.succ : ℝ≥0∞)) (tsum_eq_sum $ λ y hy, (hy $ finset.mem_univ y).elim).symm
  ... = pmf.map v.nth (uniform_of_fintype $ fin n.succ) x :
    by simp only [div_eq_mul_inv, ←ennreal.tsum_mul_right, boole_mul, map_apply,
      uniform_of_fintype_apply, fintype.card_fin])

section measure

@[simp]
lemma to_outer_measure_uniform_of_vector_apply (t : set α) :
  (uniform_of_vector v).to_outer_measure t = v.to_list.countp t / ↑(n + 1) :=
(to_outer_measure_uniform_of_list_apply v.1 _ t).trans
  (congr_arg (λ x, _ / x) (congr_arg coe v.length_coe))

@[simp]
lemma to_measure_uniform_of_vector_apply (t : set α) [measurable_space α] (ht : measurable_set t) :
  (uniform_of_vector v).to_measure t = v.to_list.countp t / ↑(n + 1) :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_vector_apply v t)

end measure

end uniform_of_vector

end pmf

-- lemma sum_ite_eq_nth {β : Type} [add_comm_monoid_with_one β]
--   (a : α) {n : ℕ} (v : vector α n) :
--   ∑ i, ite (v.nth i = a) (1 : β) 0 = ↑(v.to_list.count a) :=
-- begin
--   induction n with n hn,
--   { simp [vector.eq_nil v] },
--   { obtain ⟨x, xs, hxs⟩ := vector.exists_eq_cons v,
--     suffices : ite (x = a) 1 0 + (list.count a xs.to_list : β) =
--       ite (x = a) ((list.count a xs.to_list) + 1) (list.count a xs.to_list),
--     by simpa only [hxs, fin.sum_univ_succ, vector.to_list_cons, list.count_cons,
--       vector.nth_cons_zero, @eq_comm _ a, hn xs, fin.coe_eq_cast_succ, fin.coe_succ_eq_succ,
--       vector.nth_cons_succ, nat.cast_ite, nat.cast_succ] using this,
--     split_ifs,
--     { exact add_comm _ _ },
--     { exact zero_add _ } }
-- end

-- lemma tsum_ite_eq_vector_nth {β : Type} [add_comm_monoid_with_one β]
--   [topological_space β] [t2_space β] {n : ℕ} (v : vector α n) (a : α) :
--   ∑' (i : fin n), ite (v.nth i = a) (1 : β) 0 = ↑(v.to_list.count a) :=
-- calc ∑' (i : fin n), ite (v.nth i = a) (1 : β) 0
--   = ∑ (i : fin n), ite (v.nth i = a) (1 : β) 0 :
--     tsum_eq_sum (λ _ hb, (hb $ finset.mem_univ _).elim)
--   ... = (v.to_list.count a) : (sum_ite_eq_nth a v)
