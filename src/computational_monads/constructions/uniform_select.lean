/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.map
import computational_monads.distribution_semantics.query
import to_mathlib.uniform_of_vector
import data.vector.mem

/-!
# Computations Uniformly Drawing From Data Structures

This file defines different uniform computations derived from a `uniform_selecting` oracle.
The base construction is `uniform_fin`, suggestively denoted `$[0..n]`.
From this we build corresponding computations for `vector`, `list`, `finset`, and `fintype`,
using the notations `$ᵛ`, `$ˡ`, `$ˢ`, and `$ᵗ` respectively.

Note that the `list` and `finset` versions require explicit proofs of being nonempty,
so using `vector` and `fintype` is usually preferable when this is possible.
-/

namespace oracle_comp

variables {α β γ : Type}

open oracle_spec pmf
open_locale big_operators ennreal

section uniform_fin

/-- Randomly choose a number `0 ≤ i < n` by querying the uniform selection oracle.
  We implicitly use a `succ` call for the resulting type since `fin 0` is unihabited as a type -/
def uniform_fin (n : ℕ) : oracle_comp uniform_selecting (fin $ n + 1) :=
query n ()

notation `$[0..` n `]` := uniform_fin n

variables (n : ℕ) {m : ℕ} (i : fin m.succ)
  (oa : (fin m.succ) → oracle_comp uniform_selecting α) (x : α)

section support

@[simp] lemma support_uniform_fin : support $[0..n] = ⊤ := support_query n ()

lemma mem_support_uniform_fin_iff : i ∈ support $[0..m] :=
(support_uniform_fin n).symm ▸ set.mem_univ i

@[simp] lemma support_uniform_fin_bind : ($[0..m] >>= oa).support = ⋃ i, (oa i).support :=
by simp only [support_bind, set.Union_true]

end support

section fin_support

@[simp] lemma fin_support_uniform_fin : fin_support $[0..n] = finset.univ := fin_support_query n ()

lemma mem_fin_support_uniform_fin : i ∈ fin_support $[0..m] :=
(fin_support_uniform_fin i) ▸ finset.mem_univ i

lemma fin_support_uniform_fin_bind [decidable_eq α] :
  ($[0..m] >>= oa).fin_support = finset.bUnion finset.univ (λ i, (oa i).fin_support) :=
by {rw [fin_support_bind, fin_support_uniform_fin], congr}

end fin_support

section eval_dist

@[simp] lemma eval_dist_uniform_fin : ⁅$[0..n]⁆ = pmf.uniform_of_fintype (fin $ n + 1) := rfl

@[simp] lemma prob_output_uniform_fin : ⁅= i | $[0..m]⁆ = m.succ⁻¹ :=
by rw [prob_output.def, eval_dist_uniform_fin m, pmf.uniform_of_fintype_apply i, fintype.card_fin]

lemma prob_output_uniform_fin_bind_eq_tsum :
  ⁅= x | $[0..m] >>= oa⁆ = (∑' i, ⁅= x | oa i⁆) / m.succ :=
by simp only [prob_output_bind_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
  prob_output_uniform_fin, one_mul, mul_comm (m.succ⁻¹ : ℝ≥0∞)]

@[simp] lemma prob_output_uniform_fin_bind_eq_sum :
  ⁅= x | $[0..m] >>= oa⁆ = (∑ i, ⁅= x | oa i⁆) / m.succ :=
by simp only [prob_output_bind_eq_sum, div_eq_mul_inv, ← finset.sum_mul, one_mul,
  prob_output_uniform_fin, mul_comm (m.succ⁻¹ : ℝ≥0∞), fin_support_uniform_fin]

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_fin (e : set (fin $ m + 1)) [decidable_pred e] :
  ⁅e | $[0..m]⁆ = (fintype.card e) / (m + 1) :=
by simp only [uniform_fin, prob_event_query_eq_div, uniform_selecting_range,
  fintype.card_fin, nat.cast_add, nat.cast_one]

@[simp] lemma prob_event_uniform_fin_bind_eq_tsum (e : set α) :
  ⁅e | $[0..m] >>= oa⁆ = (∑' i, ⁅e | oa i⁆) / m.succ :=
by simp only [prob_event_bind_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
  prob_output_uniform_fin, one_mul, mul_comm (m.succ⁻¹ : ℝ≥0∞)]

lemma prob_event_uniform_fin_bind_apply_eq_sum (e : set α) :
  ⁅e | $[0..m] >>= oa⁆ = (∑ i, ⁅e | oa i⁆) / m.succ :=
by simp only [prob_event_bind_eq_sum, div_eq_mul_inv, ← finset.sum_mul, one_mul,
  prob_output_uniform_fin, mul_comm (m.succ⁻¹ : ℝ≥0∞), fin_support_uniform_fin]

end prob_event

@[pairwise_dist_equiv] lemma uniform_fin_one_dist_equiv {spec} :
  $[0..0] ≃ₚ return' !spec! 0 := by simp [dist_equiv.ext_iff]

end uniform_fin

section uniform_select_vector

/-- Randomly select an element of a vector by using `uniform_of_fin`.
  Again we need to use `succ` for the vectors type to avoid sampling an empty vector -/
def uniform_select_vector [decidable_eq α] {n : ℕ} (v : vector α (n + 1)) :
  oracle_comp uniform_selecting α := v.nth <$> $[0..n]

notation `$ᵛ` v := uniform_select_vector v

variables [decidable_eq α] {n : ℕ} (v : vector α (n + 1))
  (ob : α → oracle_comp uniform_selecting β) (x : α) (y : β)

section support

@[simp] lemma support_uniform_select_vector : ($ᵛ v).support = {a | a ∈ v.to_list} :=
(support_map $[0..n] v.nth).trans (set.ext (λ a, by simp only [vector.mem_iff_nth,
  support_uniform_fin, set.top_eq_univ, set.image_univ, set.mem_range, set.mem_set_of_eq]))

lemma support_uniform_select_vector_eq_coe_to_finset :
  ($ᵛ v).support = ↑v.to_list.to_finset :=
by simp only [support_uniform_select_vector, list.coe_to_finset]

lemma mem_support_uniform_select_vector_iff : x ∈ ($ᵛ v).support ↔ x ∈ v.to_list :=
by simp only [support_uniform_select_vector, set.mem_set_of_eq]

lemma support_uniform_select_vector_cons : ($ᵛ (x ::ᵥ v)).support = {x} ∪ ($ᵛ v).support :=
set.ext (λ x, by simp only [support_uniform_select_vector, vector.to_list_cons, list.mem_cons_iff,
  set.mem_set_of_eq, set.singleton_union, set.mem_insert_iff])

lemma support_uniform_select_vector_singleton (v : vector α 1) : ($ᵛ v).support = {v.head} :=
by simp only [support_uniform_select_vector, vector.to_list_singleton,
  list.mem_singleton, set.set_of_eq_eq_singleton]

end support

section fin_support

@[simp] lemma fin_support_uniform_select_vector : ($ᵛ v).fin_support = finset.univ.image v.nth :=
begin
  rw [fin_support_eq_iff_support_eq_coe, finset.coe_image, support_uniform_select_vector],
  exact set.ext (λ a, by simp only [vector.mem_iff_nth, set.mem_set_of_eq,
    finset.coe_univ, set.image_univ, set.mem_range]),
end

lemma fin_support_uniform_select_vector_eq_to_finset : ($ᵛ v).fin_support = v.to_list.to_finset :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_vector_eq_coe_to_finset]

lemma mem_fin_support_uniform_select_vector_iff : x ∈ ($ᵛ v).fin_support ↔ x ∈ v.to_list :=
by simp only [fin_support_uniform_select_vector, vector.mem_iff_nth,
  finset.mem_image, finset.mem_univ, exists_true_left]

lemma fin_support_uniform_select_vector_cons :
  ($ᵛ (x ::ᵥ v)).fin_support = {x} ∪ ($ᵛ v).fin_support :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_vector_cons,
  finset.coe_union, coe_fin_support_eq_support, finset.coe_singleton]

lemma fin_support_uniform_select_vector_singleton (v : vector α 1) :
  ($ᵛ v).fin_support = {v.head} := by rw [fin_support_eq_iff_support_eq_coe,
    support_uniform_select_vector_singleton, finset.coe_singleton]

end fin_support

section eval_dist

@[simp] lemma eval_dist_uniform_select_vector : ⁅$ᵛ v⁆ = pmf.uniform_of_vector v :=
by rw [uniform_select_vector, pmf.uniform_of_vector_eq_nth_map_uniform_of_fintype,
  eval_dist_map, eval_dist_uniform_fin]

@[simp] lemma prob_output_uniform_select_vector : ⁅= x | $ᵛ v⁆ = v.to_list.count x / n.succ :=
by { rw [prob_output.def, eval_dist_uniform_select_vector, pmf.uniform_of_vector_apply], congr }

lemma prob_output_uniform_select_vector_bind_eq_tsum : ⁅= y | ($ᵛ v) >>= ob⁆ =
  (∑' x, v.to_list.count x * ⁅= y | ob x⁆) / n.succ :=
begin
  simp only [prob_output_bind_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
    prob_output_uniform_select_vector],
  exact tsum_congr (λ _, by ring),
end

@[simp] lemma prob_output_uniform_select_vector_bind_eq_sum : ⁅= y | ($ᵛ v) >>= ob⁆ =
  (∑ x in v.to_list.to_finset, v.to_list.count x * ⁅= y | ob x⁆) / n.succ :=
begin
  rw [prob_output_uniform_select_vector_bind_eq_tsum],
  refine congr_arg (λ x, x / (n.succ : ℝ≥0∞)) (tsum_eq_sum $ λ x hx, _),
  rw [list.count_eq_zero_of_not_mem (λ h, hx $ list.mem_to_finset.2 h), nat.cast_zero, zero_mul],
end

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_select_vector (e : set α) [decidable_pred e] :
  ⁅e | $ᵛ v⁆ = (v.to_list.countp e) / n.succ :=
by { rw [prob_event.def, eval_dist_uniform_select_vector,
  to_outer_measure_uniform_of_vector_apply], congr }

@[simp] lemma prob_event_uniform_select_vector_bind_eq_tsum (e : set β) :
  ⁅e | ($ᵛ v) >>= ob⁆ = (∑' x, (v.to_list.count x) * ⁅e | ob x⁆) / n.succ :=
begin
  simp_rw [prob_event_bind_eq_tsum ($ᵛ v) ob e, prob_output_uniform_select_vector,
    div_eq_mul_inv, ← ennreal.tsum_mul_right],
  exact tsum_congr (λ _, by ring)
end

lemma prob_event_uniform_select_vector_bind_eq_sum (e : set β) :
  ⁅e | ($ᵛ v) >>= ob⁆ = (∑ x in v.to_list.to_finset, (v.to_list.count x) * ⁅e | ob x⁆) / n.succ :=
begin
  rw [prob_event_uniform_select_vector_bind_eq_tsum],
  refine congr_arg (λ x, x / (n.succ : ℝ≥0∞)) (tsum_eq_sum $ λ x hx, _),
  rw [list.count_eq_zero_of_not_mem (λ h, hx $ list.mem_to_finset.2 h), nat.cast_zero, zero_mul],
end

end prob_event

@[pairwise_dist_equiv] lemma uniform_select_vector_singleton_dist_equiv {spec}
  (v : vector α 1) : ($ᵛ v) ≃ₚ return' !spec! v.head :=
begin
  rw [← vector.nth_zero, uniform_select_vector],
  exact (map_dist_equiv_of_dist_equiv' rfl (by pairwise_dist_equiv)).trans
    (map_return_dist_equiv _ _)
end

end uniform_select_vector

section uniform_select_list

/-- If a list isn't empty, we can convert it to a vector and then sample from it.-/
def uniform_select_list [decidable_eq α] (xs : list α) (h : ¬ xs.empty) :
  oracle_comp uniform_selecting α :=
let v : vector α (xs.length.pred.succ) := ⟨xs, symm $ nat.succ_pred_eq_of_pos
  (list.length_pos_of_ne_nil (λ h', h $ list.empty_iff_eq_nil.2 h'))⟩ in uniform_select_vector v

notation `$ˡ` := uniform_select_list

variables [decidable_eq α] (xs : list α) (x : α) (y : β) (h : ¬ xs.empty)
  (oa : oracle_comp uniform_selecting α) (ob : α → oracle_comp uniform_selecting β)

/-- Assuming we sample from `[]`, we can treat this as any other computation,
using the provided contradictory proof that `[]` is non-empty. -/
lemma uniform_select_list_nil (h : ¬ ([] : list α).empty) :
  $ˡ [] h = oa := false.elim (h rfl)

lemma uniform_select_list_cons (h : ¬ (x :: xs).empty) :
  $ˡ (x :: xs) h = uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩ := rfl

section support

@[simp] lemma support_uniform_select_list : ($ˡ xs h).support = {x | x ∈ xs} :=
begin
  induction xs with x xs,
  { simpa only [list.empty, coe_sort_tt, not_true] using h },
  { exact set.ext (λ x', by rw [uniform_select_list,
      mem_support_uniform_select_vector_iff, vector.to_list_mk, set.mem_set_of]) }
end

lemma support_uniform_select_list_eq_coe_to_finset : ($ˡ xs h).support = ↑xs.to_finset :=
by simp only [support_uniform_select_list, list.coe_to_finset]

lemma mem_support_uniform_select_list_iff : x ∈ ($ˡ xs h).support ↔ x ∈ xs :=
by rw [oracle_comp.support_uniform_select_list, set.mem_set_of_eq]

end support

section fin_support

@[simp] lemma fin_support_uniform_select_list : ($ˡ xs h).fin_support = xs.to_finset :=
(fin_support_eq_iff_support_eq_coe _ _).2 (set.ext $ λ x, by simp only [finset.mem_coe,
  support_uniform_select_list, set.mem_set_of_eq, list.mem_to_finset])

lemma mem_fin_support_uniform_select_list_iff : x ∈ ($ˡ xs h).fin_support ↔ x ∈ xs :=
by rw [fin_support_uniform_select_list, list.mem_to_finset]

end fin_support

section eval_dist

lemma eval_dist_uniform_select_list_nil (h : ¬ ([] : list α).empty) (p : pmf α) :
  ⁅$ˡ [] h⁆ = p := false.elim (h rfl)

@[simp] lemma eval_dist_uniform_select_list : ⁅$ˡ xs h⁆ = pmf.uniform_of_list xs h :=
begin
  induction xs with x xs,
  { exact eval_dist_uniform_select_list_nil h _ },
  { simpa only [uniform_select_list_cons, eval_dist_uniform_select_vector] }
end

@[simp] lemma prob_output_uniform_select_list : ⁅= x | $ˡ xs h⁆ = xs.count x / xs.length :=
by { rw [prob_output.def, eval_dist_uniform_select_list, pmf.uniform_of_list_apply], congr }

lemma prob_output_uniform_select_list_bind_eq_tsum :
  ⁅= y | $ˡ xs h >>= ob⁆ = (∑' x, xs.count x * ⁅= y | ob x⁆) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_output_uniform_select_vector_bind_eq_tsum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

lemma prob_output_uniform_select_list_bind_eq_sum :
  ⁅= y | $ˡ xs h >>= ob⁆ = (∑ x in xs.to_finset, xs.count x * ⁅= y | ob x⁆) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_output_uniform_select_vector_bind_eq_sum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_select_list (e : set α) [decidable_pred e] :
  ⁅e | $ˡ xs h⁆ = xs.countp e / xs.length :=
by { rw [prob_event.def, eval_dist_uniform_select_list,
  to_outer_measure_uniform_of_list_apply], congr }

@[simp] lemma prob_event_uniform_select_list_bind_eq_tsum (e : set β) :
  ⁅e | $ˡ xs h >>= ob⁆ = (∑' x, xs.count x * ⁅e | ob x⁆) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_event_uniform_select_vector_bind_eq_tsum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

lemma prob_event_uniform_select_list_bind_eq_sum (e : set β) :
  ⁅e | $ˡ xs h >>= ob⁆ = (∑ x in xs.to_finset, xs.count x * ⁅e | ob x⁆) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_event_uniform_select_vector_bind_eq_sum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

end prob_event

lemma uniform_select_list_singleton_dist_equiv {spec} (h : ¬ [x].empty) :
  $ˡ [x] h ≃ₚ return' !spec! x := by pairwise_dist_equiv

end uniform_select_list

section uniform_select_finset

/-- We can sample randomly from a `finset` by converting to a list and then sampling that. -/
noncomputable def uniform_select_finset [decidable_eq α]
  (bag : finset α) (h : bag.nonempty) : oracle_comp uniform_selecting α :=
uniform_select_list bag.to_list (finset.nonempty.not_empty_to_list h)

notation `$ˢ` := uniform_select_finset

variables [decidable_eq α] (bag : finset α) (h : bag.nonempty)
  (ob : α → oracle_comp uniform_selecting β) (x : α) (y : β)

/-- Assuming we sample from `∅`, we can treat this as any other computation,
using the provided contradictory proof that `∅` is non-empty. -/
lemma uniform_select_finset_empty (h : (∅ : finset α).nonempty)
  (oa : oracle_comp uniform_selecting α) : $ˢ ∅ h = oa :=
false.elim (finset.nonempty.ne_empty h rfl)

section support

@[simp] lemma support_uniform_select_finset : ($ˢ bag h).support = ↑bag :=
by simp only [uniform_select_finset, support_uniform_select_list,
  finset.mem_to_list, finset.set_of_mem]

lemma mem_support_uniform_select_finset_iff : x ∈ ($ˢ bag h).support ↔ x ∈ bag :=
by rw [support_uniform_select_finset, finset.mem_coe]

end support

section fin_support

@[simp] lemma fin_support_uniform_select_finset : ($ˢ bag h).fin_support = bag :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_finset]

lemma mem_fin_support_uniform_select_finset_iff : x ∈ ($ˢ bag h).fin_support ↔ x ∈ bag :=
by rw [fin_support_uniform_select_finset]

end fin_support

section eval_dist

@[simp] lemma eval_dist_uniform_select_finset : ⁅$ˢ bag h⁆ = pmf.uniform_of_finset bag h :=
(pmf.ext $ λ x, by simp only [uniform_select_finset, div_eq_mul_inv, eval_dist_uniform_select_list,
  uniform_of_list_apply, finset.count_to_list, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, finset.length_to_list, boole_mul, uniform_of_finset_apply])

@[simp] lemma prob_output_uniform_select_finset : ⁅= x | $ˢ bag h⁆ = ite (x ∈ bag) bag.card⁻¹ 0 :=
by { rw [prob_output.def, eval_dist_uniform_select_finset, pmf.uniform_of_finset_apply], congr }

lemma prob_output_uniform_select_finset_bind_eq_tsum :
  ⁅= y | $ˢ bag h >>= ob⁆ = (∑' x, ite (x ∈ bag) ⁅= y | ob x⁆ 0) / bag.card :=
by simp only [uniform_select_finset, prob_output_uniform_select_list_bind_eq_tsum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

@[simp] lemma prob_output_uniform_select_finset_bind_eq_sum  :
  ⁅= y | $ˢ bag h >>= ob⁆ = (∑ x in bag, ⁅= y | ob x⁆) / bag.card :=
by simp only [uniform_select_finset, prob_output_uniform_select_list_bind_eq_sum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_select_finset (e : set α) [decidable_pred e] :
  ⁅e | $ˢ bag h⁆ = (bag.filter (∈ e)).card / bag.card :=
by { rw [prob_event.def, eval_dist_uniform_select_finset,
  to_outer_measure_uniform_of_finset_apply], congr }

lemma prob_event_uniform_select_finset_bind_eq_tsum (e : set β) :
  ⁅e | $ˢ bag h >>= ob⁆ = (∑' x, ite (x ∈ bag) ⁅e | ob x⁆ 0) / bag.card :=
by simp only [uniform_select_finset, prob_event_uniform_select_list_bind_eq_tsum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

lemma prob_event_uniform_select_finset_bind_eq_sum (e : set β) :
  ⁅e | $ˢ bag h >>= ob⁆ = (∑ x in bag, ⁅e | ob x⁆) / bag.card :=
by simp only [uniform_select_finset, prob_event_uniform_select_list_bind_eq_sum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

end prob_event

@[pairwise_dist_equiv] lemma uniform_select_finset_singleton_dist_equiv {spec}
  (h : finset.nonempty {x}) : $ˢ {x} h ≃ₚ return' !spec! x :=
by simp only [uniform_select_finset, finset.to_list_singleton,
  uniform_select_list_singleton_dist_equiv]

end uniform_select_finset

section uniform_select_fintype

/-- We can select randomly from a fintyp by using the `finset` corresponding to the `fintype`.
  Again we need to use axiom of choice so this operation is noncomputable. -/
noncomputable def uniform_select_fintype (α : Type) [fintype α] [nonempty α]
  [decidable_eq α] : oracle_comp uniform_selecting α :=
uniform_select_finset finset.univ finset.univ_nonempty

notation `$ᵗ` := uniform_select_fintype

variables (α) [fintype α] [nonempty α] [decidable_eq α]
  (ob : α → oracle_comp uniform_selecting β) (x : α) (y : β)

section support

@[simp] lemma support_uniform_select_fintype : ($ᵗ α).support = ⊤ :=
by rw [uniform_select_fintype, support_uniform_select_finset,
  set.top_eq_univ, finset.coe_eq_univ]

lemma mem_support_uniform_select_fintype : x ∈ ($ᵗ α).support :=
by simp only [support_uniform_select_fintype]

end support

section fin_support

@[simp] lemma fin_support_uniform_select_fintype : ($ᵗ α).fin_support = finset.univ :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_fintype,
  set.top_eq_univ, finset.coe_univ]

lemma mem_fin_support_uniform_select_fintype : x ∈ ($ᵗ α).fin_support :=
by simp only [fin_support_uniform_select_fintype, finset.mem_univ]

end fin_support

section eval_dist

@[simp] lemma eval_dist_uniform_select_fintype : ⁅$ᵗ α⁆ = pmf.uniform_of_fintype α :=
by rw [uniform_select_fintype, eval_dist_uniform_select_finset, pmf.uniform_of_fintype]

@[simp] lemma prob_output_uniform_select_fintype : ⁅= x | $ᵗ α⁆ = (fintype.card α)⁻¹ :=
by rw [prob_output.def, eval_dist_uniform_select_fintype, pmf.uniform_of_fintype_apply]

lemma prob_output_uniform_select_fintype_bind_eq_tsum :
  ⁅= y | $ᵗ α >>= ob⁆ = (∑' x, ⁅= y | ob x⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_output_uniform_select_finset_bind_eq_tsum,
  finset.mem_univ, if_true, finset.card_univ]

@[simp] lemma eval_dist_uniform_select_fintype_bind_apply_eq_sum :
  ⁅= y | $ᵗ α >>= ob⁆ = (∑ x, ⁅= y | ob x⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_output_uniform_select_finset_bind_eq_sum,
  finset.mem_univ, if_true, finset.card_univ]

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_select_fintype (e : set α) [decidable_pred e] :
  ⁅e | $ᵗ α⁆ = fintype.card e / fintype.card α :=
by { simp only [prob_event.def, eval_dist_uniform_select_fintype,
  to_outer_measure_uniform_of_fintype_apply, finset.mem_univ, if_true, finset.card_univ], congr }

lemma prob_event_uniform_select_fintype_bind_eq_tsum (e : set β) :
  ⁅e | $ᵗ α >>= ob⁆ = (∑' a, ⁅e | ob a⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_event_uniform_select_finset_bind_eq_tsum,
  finset.mem_univ, if_true, finset.card_univ]

@[simp] lemma prob_event_uniform_select_fintype_bind_eq_sum (e : set β) :
  ⁅e | $ᵗ α >>= ob⁆ = (∑ a, ⁅e | ob a⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_event_uniform_select_finset_bind_eq_sum,
  finset.mem_univ, if_true, finset.card_univ]

end prob_event

lemma uniform_select_fintype_dist_equiv_return {spec} {α : Type} [unique α] :
  $ᵗ α ≃ₚ return' !spec! default := by pairwise_dist_equiv

@[pairwise_dist_equiv] lemma uniform_select_fintype_range {spec : oracle_spec} {i : spec.ι}
  (t : spec.domain i) : $ᵗ (spec.range i) ≃ₚ query i t :=
by simp [dist_equiv.ext_iff, prob_output_query_eq_inv]

end uniform_select_fintype

end oracle_comp