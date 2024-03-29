/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.query
import computational_monads.distribution_semantics.prod
import to_mathlib.uniform_of_vector

/-!
# Computations Uniformly Drawing From Data Structures

This file defines different uniform computations derived from a `unif_spec` oracle.
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
def uniform_fin (n : ℕ) : oracle_comp unif_spec (fin $ n + 1) :=
query n ()

notation `$[0..` n `]` := uniform_fin n

variables (n : ℕ) {m : ℕ} (i : fin m.succ)
  (oa : (fin m.succ) → oracle_comp unif_spec α) (x : α)

section support

@[simp] lemma support_uniform_fin : support $[0..n] = ⊤ := support_query n ()

lemma mem_support_uniform_fin_iff : i ∈ support $[0..m] :=
(support_uniform_fin m).symm ▸ set.mem_univ i

@[simp] lemma support_uniform_fin_bind : ($[0..m] >>= oa).support = ⋃ i, (oa i).support :=
by simp only [support_bind, support_uniform_fin, set.Union_true]

end support

section fin_support

@[simp] lemma fin_support_uniform_fin : fin_support $[0..n] = finset.univ := fin_support_query _ ()

lemma mem_fin_support_uniform_fin : i ∈ fin_support $[0..m] :=
(fin_support_uniform_fin m).symm ▸ finset.mem_univ i

lemma fin_support_uniform_fin_bind [decidable_eq α] :
  ($[0..m] >>= oa).fin_support = finset.bUnion finset.univ (λ i, (oa i).fin_support) :=
by {rw [fin_support_bind, fin_support_uniform_fin] }

end fin_support

lemma uniform_fin_zero_dist_equiv : $[0..0] ≃ₚ (return 0 : oracle_comp unif_spec (fin 1)) :=
by simp [dist_equiv_return_iff', set.ext_iff]

section eval_dist

@[simp] lemma eval_dist_uniform_fin : ⁅$[0..n]⁆ = pmf.uniform_of_fintype (fin $ n + 1) :=
by simpa only [uniform_fin, eval_dist_query]

@[simp] lemma prob_output_uniform_fin : ⁅= i | $[0..m]⁆ = (↑(m + 1))⁻¹ :=
by rw [prob_output.def, eval_dist_uniform_fin m, pmf.uniform_of_fintype_apply i,
  fintype.card_fin, nat.cast_succ]

lemma prob_output_uniform_fin_bind_eq_tsum :
  ⁅= x | $[0..m] >>= oa⁆ = (∑' i, ⁅= x | oa i⁆) / ↑(m + 1) :=
by simp only [prob_output_bind_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
  prob_output_uniform_fin, one_mul, mul_comm (m.succ⁻¹ : ℝ≥0∞)]

@[simp] lemma prob_output_uniform_fin_bind_eq_sum :
  ⁅= x | $[0..m] >>= oa⁆ = (∑ i, ⁅= x | oa i⁆) / ↑(m + 1) :=
by simp only [prob_output_bind_eq_sum, div_eq_mul_inv, ← finset.sum_mul, one_mul,
  prob_output_uniform_fin, mul_comm (m.succ⁻¹ : ℝ≥0∞), fin_support_uniform_fin]

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_fin (p : fin (m + 1) → Prop) [decidable_pred p] :
  ⁅p | $[0..m]⁆ = (finset.univ.filter p).card / ↑(m + 1) :=
by simp_rw [prob_event_eq_sum_filter, fin_support_uniform_fin,
  prob_output_uniform_fin, finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

lemma prob_event_uniform_fin_bind_eq_tsum (p : α → Prop) :
  ⁅p | $[0..m] >>= oa⁆ = (∑' i, ⁅p | oa i⁆) / ↑(m + 1) :=
by simp only [prob_event_bind_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
  prob_output_uniform_fin, one_mul, mul_comm (m.succ⁻¹ : ℝ≥0∞)]

@[simp] lemma prob_event_uniform_fin_bind_apply_eq_sum (p : α → Prop) :
  ⁅p | $[0..m] >>= oa⁆ = (∑ i, ⁅p | oa i⁆) / ↑(m + 1) :=
by simp only [prob_event_bind_eq_sum, div_eq_mul_inv, ← finset.sum_mul, one_mul,
  prob_output_uniform_fin, mul_comm (m.succ⁻¹ : ℝ≥0∞), fin_support_uniform_fin]

end prob_event

@[pairwise_dist_equiv] lemma uniform_fin_one_dist_equiv {spec} :
  $[0..0] ≃ₚ return' !spec! 0 := by simp [dist_equiv.ext_iff]

end uniform_fin

section uniform_select_vector

/-- Randomly select an element of a vector by using `uniform_of_fin`.
Again we need to use `succ` for the vectors type to avoid sampling an empty vector -/
def uniform_select_vector {n : ℕ} (v : vector α (n + 1)) :
  oracle_comp unif_spec α := v.nth <$> $[0..n]

notation `$ᵛ` v := uniform_select_vector v

variables {n : ℕ} (v : vector α (n + 1))
  (ob : α → oracle_comp unif_spec β) (x : α) (y : β)

section support

@[simp] lemma support_uniform_select_vector : ($ᵛ v).support = {a | a ∈ v.to_list} :=
(support_map $[0..n] v.nth).trans (set.ext (λ a, by simp only [vector.mem_iff_nth,
  support_uniform_fin, set.top_eq_univ, set.image_univ, set.mem_range, set.mem_set_of_eq]))

lemma support_uniform_select_vector_eq_coe_to_finset [decidable_eq α] :
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

variable [decidable_eq α]

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
  finset.coe_union, coe_fin_support, finset.coe_singleton]

lemma fin_support_uniform_select_vector_singleton (v : vector α 1) :
  ($ᵛ v).fin_support = {v.head} := by rw [fin_support_eq_iff_support_eq_coe,
    support_uniform_select_vector_singleton, finset.coe_singleton]

end fin_support

section eval_dist

@[simp] lemma eval_dist_uniform_select_vector : ⁅$ᵛ v⁆ = pmf.uniform_of_vector v :=
by rw [uniform_select_vector, pmf.uniform_of_vector_eq_nth_map_uniform_of_fintype,
  eval_dist_map, eval_dist_uniform_fin]

@[simp] lemma prob_output_uniform_select_vector [decidable_eq α] :
  ⁅= x | $ᵛ v⁆ = v.to_list.count x / n.succ :=
by { rw [prob_output.def, eval_dist_uniform_select_vector, pmf.uniform_of_vector_apply], congr }

lemma prob_output_uniform_select_vector_bind_eq_tsum [decidable_eq α] :
  ⁅= y | ($ᵛ v) >>= ob⁆ = (∑' x, v.to_list.count x * ⁅= y | ob x⁆) / n.succ :=
begin
  simp only [prob_output_bind_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
    prob_output_uniform_select_vector],
  exact tsum_congr (λ _, by ring),
end

@[simp] lemma prob_output_uniform_select_vector_bind_eq_sum [decidable_eq α] :
  ⁅= y | ($ᵛ v) >>= ob⁆ = (∑ x in v.1.to_finset, v.1.count x * ⁅= y | ob x⁆) / n.succ :=
begin
  rw [prob_output_uniform_select_vector_bind_eq_tsum],
  refine congr_arg (λ x, x / (n.succ : ℝ≥0∞)) (tsum_eq_sum $ λ x hx, _),
  rw [vector.to_list, list.count_eq_zero_of_not_mem (λ h, hx $ list.mem_to_finset.2 h),
    nat.cast_zero, zero_mul],
end

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_select_vector (p : α → Prop) [decidable_pred p] :
  ⁅p | $ᵛ v⁆ = (v.to_list.countp p) / n.succ :=
by { rw [prob_event.def, eval_dist_uniform_select_vector,
  to_outer_measure_uniform_of_vector_apply], congr }

lemma prob_event_uniform_select_vector_bind_eq_tsum [decidable_eq α] (p : β → Prop) :
  ⁅p | ($ᵛ v) >>= ob⁆ = (∑' x, (v.to_list.count x) * ⁅p | ob x⁆) / n.succ :=
begin
  simp_rw [prob_event_bind_eq_tsum ($ᵛ v) ob p, prob_output_uniform_select_vector,
    div_eq_mul_inv, ← ennreal.tsum_mul_right],
  exact tsum_congr (λ _, by ring)
end

@[simp] lemma prob_event_uniform_select_vector_bind_eq_sum [decidable_eq α] (p : β → Prop) :
  ⁅p | ($ᵛ v) >>= ob⁆ = (∑ x in v.to_list.to_finset, (v.to_list.count x) * ⁅p | ob x⁆) / n.succ :=
begin
  rw [prob_event_uniform_select_vector_bind_eq_tsum],
  refine congr_arg (λ x, x / (n.succ : ℝ≥0∞)) (tsum_eq_sum $ λ x hx, _),
  rw [list.count_eq_zero_of_not_mem (λ h, hx $ list.mem_to_finset.2 h), nat.cast_zero, zero_mul],
end

end prob_event

@[pairwise_dist_equiv] lemma uniform_select_vector_singleton_dist_equiv
  (v : vector α 1) : ($ᵛ v) ≃ₚ (return v.head : oracle_comp unif_spec α) :=
begin
  rw [← vector.nth_zero, uniform_select_vector],
  rw_dist_equiv [uniform_fin_zero_dist_equiv, return_bind_dist_equiv]
end

end uniform_select_vector

section uniform_select_list

/-- If a list isn't empty, we can convert it to a vector and then sample from it.-/
def uniform_select_list (xs : list α) (h : ¬ xs.empty) :
  oracle_comp unif_spec α :=
let v : vector α (xs.length.pred.succ) := ⟨xs, symm $ nat.succ_pred_eq_of_pos
  (list.length_pos_of_ne_nil (λ h', h $ list.empty_iff_eq_nil.2 h'))⟩ in uniform_select_vector v

notation `$ˡ` := uniform_select_list

variables (xs : list α) (x : α) (y : β) (h : ¬ xs.empty)
  (oa : oracle_comp unif_spec α) (ob : α → oracle_comp unif_spec β)

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

lemma support_uniform_select_list_eq_coe_to_finset [decidable_eq α] :
  ($ˡ xs h).support = ↑xs.to_finset :=
by simp only [support_uniform_select_list, list.coe_to_finset]

lemma mem_support_uniform_select_list_iff : x ∈ ($ˡ xs h).support ↔ x ∈ xs :=
by rw [oracle_comp.support_uniform_select_list, set.mem_set_of_eq]

end support

section fin_support

variable [decidable_eq α]

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

variable [decidable_eq α]

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

@[simp] lemma prob_event_uniform_select_list (p : α → Prop) [decidable_pred p] :
  ⁅p | $ˡ xs h⁆ = xs.countp p / xs.length :=
by { rw [prob_event.def, eval_dist_uniform_select_list,
  to_outer_measure_uniform_of_list_apply], congr }

lemma prob_event_uniform_select_list_bind_eq_tsum [decidable_eq α] (p : β → Prop) :
  ⁅p | $ˡ xs h >>= ob⁆ = (∑' x, xs.count x * ⁅p | ob x⁆) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_event_uniform_select_vector_bind_eq_tsum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

@[simp] lemma prob_event_uniform_select_list_bind_eq_sum [decidable_eq α] (p : β → Prop) :
  ⁅p | $ˡ xs h >>= ob⁆ = (∑ x in xs.to_finset, xs.count x * ⁅p | ob x⁆) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_event_uniform_select_vector_bind_eq_sum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

end prob_event

lemma uniform_select_list_singleton_dist_equiv (h : ¬ [x].empty) :
  $ˡ [x] h ≃ₚ (return x : oracle_comp unif_spec α) := by pairwise_dist_equiv

end uniform_select_list

section uniform_select_finset

/-- We can sample randomly from a `finset` by converting to a list and then sampling that. -/
noncomputable def uniform_select_finset (bag : finset α) (h : bag.nonempty) :
  oracle_comp unif_spec α :=
uniform_select_list bag.to_list (finset.nonempty.not_empty_to_list h)

notation `$ˢ` := uniform_select_finset

variables (bag : finset α) (h : bag.nonempty)
  (ob : α → oracle_comp unif_spec β) (x : α) (y : β)

/-- Assuming we sample from `∅`, we can treat this as any other computation,
using the provided contradictory proof that `∅` is non-empty. -/
lemma uniform_select_finset_empty (h : (∅ : finset α).nonempty)
  (oa : oracle_comp unif_spec α) : $ˢ ∅ h = oa :=
false.elim (finset.nonempty.ne_empty h rfl)

section support

@[simp] lemma support_uniform_select_finset : ($ˢ bag h).support = ↑bag :=
by simp only [uniform_select_finset, support_uniform_select_list,
  finset.mem_to_list, finset.set_of_mem]

lemma mem_support_uniform_select_finset_iff : x ∈ ($ˢ bag h).support ↔ x ∈ bag :=
by rw [support_uniform_select_finset, finset.mem_coe]

end support

section fin_support

variable [decidable_eq α]

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

@[simp] lemma prob_output_uniform_select_finset [decidable_eq α] :
  ⁅= x | $ˢ bag h⁆ = ite (x ∈ bag) bag.card⁻¹ 0 :=
by { rw [prob_output.def, eval_dist_uniform_select_finset, pmf.uniform_of_finset_apply], congr }

lemma prob_output_uniform_select_finset_bind_eq_tsum [decidable_eq α] :
  ⁅= y | $ˢ bag h >>= ob⁆ = (∑' x, ite (x ∈ bag) ⁅= y | ob x⁆ 0) / bag.card :=
by simp only [uniform_select_finset, prob_output_uniform_select_list_bind_eq_tsum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

@[simp] lemma prob_output_uniform_select_finset_bind_eq_sum [decidable_eq α] :
  ⁅= y | $ˢ bag h >>= ob⁆ = (∑ x in bag, ⁅= y | ob x⁆) / bag.card :=
by simp only [uniform_select_finset, prob_output_uniform_select_list_bind_eq_sum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

end eval_dist

section prob_event

@[simp] lemma prob_event_uniform_select_finset (p : α → Prop) [decidable_pred p] :
  ⁅p | $ˢ bag h⁆ = (bag.filter p).card / bag.card :=
by { rw [prob_event.def, eval_dist_uniform_select_finset,
  to_outer_measure_uniform_of_finset_apply], congr }

lemma prob_event_uniform_select_finset_bind_eq_tsum [decidable_eq α] (p : β → Prop) :
  ⁅p | $ˢ bag h >>= ob⁆ = (∑' x, ite (x ∈ bag) ⁅p | ob x⁆ 0) / bag.card :=
by simp only [uniform_select_finset, prob_event_uniform_select_list_bind_eq_tsum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

@[simp] lemma prob_event_uniform_select_finset_bind_eq_sum [decidable_eq α] (p : β → Prop) :
  ⁅p | $ˢ bag h >>= ob⁆ = (∑ x in bag, ⁅p | ob x⁆) / bag.card :=
by simp only [uniform_select_finset, prob_event_uniform_select_list_bind_eq_sum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

end prob_event

@[pairwise_dist_equiv] lemma uniform_select_finset_singleton_dist_equiv
  (h : finset.nonempty {x}) : $ˢ {x} h ≃ₚ (return x : oracle_comp unif_spec α) :=
by simp only [uniform_select_finset, finset.to_list_singleton,
  uniform_select_list_singleton_dist_equiv]

end uniform_select_finset

section uniform_select_fintype

/-- We can select randomly from a fintyp by using the `finset` corresponding to the `fintype`.
  Again we need to use axiom of choice so this operation is noncomputable. -/
noncomputable def uniform_select_fintype (α : Type) [fintype α] [nonempty α] :
  oracle_comp unif_spec α :=
uniform_select_finset finset.univ finset.univ_nonempty

notation `$ᵗ` := uniform_select_fintype

variables (α) [fintype α] [nonempty α]
  (ob : α → oracle_comp unif_spec β) (x : α) (y : β)

section support

@[simp] lemma support_uniform_select_fintype : ($ᵗ α).support = ⊤ :=
by rw [uniform_select_fintype, support_uniform_select_finset,
  set.top_eq_univ, finset.coe_eq_univ]

lemma mem_support_uniform_select_fintype : x ∈ ($ᵗ α).support :=
by simp only [support_uniform_select_fintype]

end support

section fin_support

variable [decidable_eq α]

@[simp] lemma fin_support_uniform_select_fintype : ($ᵗ α).fin_support = finset.univ :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_fintype,
  set.top_eq_univ, finset.coe_univ]

lemma mem_fin_support_uniform_select_fintype : x ∈ ($ᵗ α).fin_support :=
by simp only [fin_support_uniform_select_fintype, finset.mem_univ]

end fin_support

section eval_dist

@[simp] lemma eval_dist_uniform_select_fintype : ⁅$ᵗ α⁆ = pmf.uniform_of_fintype α :=
by rw [uniform_select_fintype, eval_dist_uniform_select_finset, pmf.uniform_of_fintype]

end eval_dist

section prob_output

@[simp] lemma prob_output_uniform_select_fintype : ⁅= x | $ᵗ α⁆ = (fintype.card α)⁻¹ :=
by rw [prob_output.def, eval_dist_uniform_select_fintype, pmf.uniform_of_fintype_apply]

lemma prob_output_uniform_select_fintype_bind_eq_tsum [decidable_eq α] :
  ⁅= y | $ᵗ α >>= ob⁆ = (∑' x, ⁅= y | ob x⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_output_uniform_select_finset_bind_eq_tsum,
  finset.mem_univ, if_true, finset.card_univ]

lemma prob_output_uniform_select_fintype_bind_apply_eq_sum [decidable_eq α] :
  ⁅= y | $ᵗ α >>= ob⁆ = (∑ x, ⁅= y | ob x⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_output_uniform_select_finset_bind_eq_sum,
  finset.mem_univ, if_true, finset.card_univ]

@[simp] lemma prob_output_uniform_select_fintype_bind_const_bind_eq
  {α : Type} [fintype α] [inhabited α] [decidable_eq α]
  (oa : oracle_comp unif_spec α) :
  ⁅= tt | do {x ← $ᵗ α, x' ← oa, return (x = x' : bool)}⁆ = (fintype.card α)⁻¹ :=
begin
  simp only [prob_output_bind_eq_tsum, ennreal.tsum_mul_left, prob_output_uniform_select_fintype,
    prob_output_return, bool.tt_eq_to_bool_iff, coe_sort_tt, if_true],
  rw [ennreal.tsum_comm],
  simp_rw [ennreal.tsum_mul_left, tsum_ite_eq, mul_one, tsum_prob_output, mul_one]
end

lemma prob_output_uniform_select_fintype_bind_bind_eq_of_const
  {α : Type} [fintype α] [inhabited α] [decidable_eq α]
  (oa : α → oracle_comp unif_spec α)
  (hoa : ∃ oa₀ : oracle_comp unif_spec α, ∀ x, oa x ≃ₚ oa₀) :
  ⁅= tt | do {x ← $ᵗ α, x' ← oa x, return (x = x' : bool)}⁆ = (fintype.card α)⁻¹ :=
begin
  obtain ⟨oa₀, h⟩ := hoa,
  refine trans _ (prob_output_uniform_select_fintype_bind_const_bind_eq oa₀),
  rw_dist_equiv [h],
end

end prob_output

section prob_event

@[simp] lemma prob_event_uniform_select_fintype (p : α → Prop) [decidable_pred p] :
  ⁅p | $ᵗ α⁆ = (finset.univ.filter p).card / fintype.card α :=
by simp only [prob_event_eq_sum_filter_univ, div_eq_mul_inv,
  prob_output_uniform_select_fintype, finset.sum_const, nsmul_eq_mul]

lemma prob_event_uniform_select_fintype_bind_eq_tsum [decidable_eq α] (p : β → Prop) :
  ⁅p | $ᵗ α >>= ob⁆ = (∑' a, ⁅p | ob a⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_event_uniform_select_finset_bind_eq_tsum,
  finset.mem_univ, if_true, finset.card_univ]

@[simp] lemma prob_event_uniform_select_fintype_bind_eq_sum [decidable_eq α] (p : β → Prop) :
  ⁅p | $ᵗ α >>= ob⁆ = (∑ a, ⁅p | ob a⁆) / fintype.card α :=
by simp only [uniform_select_fintype, prob_event_uniform_select_finset_bind_eq_sum,
  finset.mem_univ, if_true, finset.card_univ]

end prob_event

lemma uniform_select_fintype_dist_equiv_return {α : Type} [unique α] :
  $ᵗ α ≃ₚ (return default : oracle_comp unif_spec α) := by pairwise_dist_equiv

@[pairwise_dist_equiv] lemma uniform_select_fintype_range {spec : oracle_spec} {i : spec.ι}
  (t : spec.domain i) : $ᵗ (spec.range i) ≃ₚ query i t :=
by simp [dist_equiv.ext_iff, prob_output_query_eq_inv]

lemma prob_output_uniform_select_fintype_bind_bij [decidable_eq α]
  (f : α → α) (hf : f.bijective) (ob : α → oracle_comp unif_spec β)
  (y : β) : ⁅= y | $ᵗ α >>= ob⁆ = ⁅= y | $ᵗ α >>= (ob ∘ f)⁆ :=
begin
  simp [prob_output_uniform_select_fintype_bind_apply_eq_sum],
  refine congr_arg (λ r : ℝ≥0∞, r / fintype.card α) _,
  obtain ⟨g, hg⟩ := function.bijective_iff_has_inverse.1 hf,
  simp [function.left_inverse, function.right_inverse] at hg,
  refine finset.sum_bij' (λ x _, g x) (λ _ _, finset.mem_univ _) _
    (λ x _, f x) (λ _ _, finset.mem_univ _) _ _; simp [hg.1, hg.2],
end

lemma uniform_select_fintype_bind_bij_dist_equiv [decidable_eq α]
  (f : α → α) (hf : f.bijective) (ob : α → oracle_comp unif_spec β) :
  $ᵗ α >>= ob ≃ₚ $ᵗ α >>= (ob ∘ f) :=
dist_equiv.ext (λ y, prob_output_uniform_select_fintype_bind_bij α f hf ob y)

lemma map_uniform_select_fintype_dist_equiv_of_bijective {α β : Type} [fintype α] [nonempty α]
  [fintype β] [nonempty β] (f : α → β) (hf : f.bijective) : f <$> $ᵗ α ≃ₚ $ᵗ β :=
begin
  refine dist_equiv.ext (λ y, _),
  obtain ⟨g, hgf, hfg⟩ := function.bijective_iff_has_inverse.1 hf,
  rw [← hfg y, prob_output_uniform_select_fintype, prob_output_map_of_injective ($ᵗ α) (g y) hf.1,
    prob_output_uniform_select_fintype, fintype.card_of_bijective hf],
end

lemma uniform_select_fintype_prod_dist_equiv {α β : Type}
  [nonempty α] [fintype α] [nonempty β] [fintype β] :
  $ᵗ (α × β) ≃ₚ prod.mk <$> $ᵗ α <*> $ᵗ β :=
begin
  refine dist_equiv.ext (λ z, _),
  simp only [ennreal.tsum_mul_left, prob_output_uniform_select_fintype,
    fintype.card_prod, nat.cast_mul, prob_output_seq_map_eq_tsum', prob_output_prod_return,
    tsum_prob_output_return, mul_one],
  exact ennreal.mul_inv (or.inr (ennreal.nat_ne_top _)) (or.inl (ennreal.nat_ne_top _)),
end

lemma prob_output_uniform_select_fintype_prod {α β : Type}
  [nonempty α] [fintype α] [nonempty β] [fintype β]
  (oc : α → β → oracle_comp unif_spec γ) (z : γ) :
  ⁅= z | do {x ←$ᵗ α, y ←$ᵗ β, oc x y}⁆ =
    ⁅= z | do {xy ←$ᵗ (α × β), oc xy.1 xy.2}⁆ :=
begin
  simp [prob_output_bind_eq_tsum, tsum_prod', ennreal.tsum_mul_left],
  rw [ennreal.mul_inv (or.inr (ennreal.nat_ne_top _)) (or.inl (ennreal.nat_ne_top _)), mul_assoc],
end

end uniform_select_fintype

end oracle_comp