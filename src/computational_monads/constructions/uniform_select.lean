/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.prob_event
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
@[derive decidable] def uniform_fin (n : ℕ) : oracle_comp uniform_selecting (fin $ n + 1) :=
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

@[simp] lemma fin_support_uniform_fin : fin_support $[0..n] = finset.univ := fin_support_query n ()

lemma mem_fin_support_uniform_fin : i ∈ fin_support $[0..m] :=
(fin_support_uniform_fin i) ▸ finset.mem_univ i

lemma fin_support_uniform_fin_bind [decidable_eq α] [∀ i, (oa i).decidable] :
  ($[0..m] >>= oa).fin_support = finset.bUnion finset.univ (λ i, (oa i).fin_support) :=
by {rw [fin_support_bind, fin_support_uniform_fin], congr}

end support

section distribution_semantics

open distribution_semantics

@[simp] lemma eval_dist_uniform_fin : ⦃$[0..n]⦄ = pmf.uniform_of_fintype (fin $ n + 1) := rfl

lemma eval_dist_uniform_fin_apply : ⦃$[0..m]⦄ i = m.succ⁻¹ :=
by rw [eval_dist_uniform_fin m, pmf.uniform_of_fintype_apply i, fintype.card_fin (m + 1)]

lemma eval_dist_uniform_fin_bind_apply_eq_tsum : ⦃$[0..m] >>= oa⦄ x = (∑' i, ⦃oa i⦄ x) / m.succ :=
by simp only [eval_dist_bind_apply_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
  eval_dist_uniform_fin_apply, one_mul, mul_comm (m.succ⁻¹ : ℝ≥0∞)]

lemma eval_dist_uniform_fin_bind_apply_eq_sum : ⦃$[0..m] >>= oa⦄ x = (∑ i, ⦃oa i⦄ x) / m.succ :=
by simp only [eval_dist_bind_apply_eq_sum, div_eq_mul_inv, ← finset.sum_mul, one_mul,
  eval_dist_uniform_fin_apply, mul_comm (m.succ⁻¹ : ℝ≥0∞), fin_support_uniform_fin]

@[simp] lemma prob_event_uniform_fin (e : set (fin $ m + 1)) [decidable_pred e] :
  ⦃e | $[0..m]⦄ = (fintype.card e) / (m + 1) :=
by simp only [uniform_fin, prob_event_query, uniform_selecting_range,
  fintype.card_fin, nat.cast_add, nat.cast_one]

@[simp] lemma prob_event_uniform_fin_bind_eq_tsum (e : set α) :
  ⦃e | $[0..m] >>= oa⦄ = (∑' i, ⦃e | oa i⦄) / m.succ :=
by simp only [prob_event_bind_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
  eval_dist_uniform_fin_apply, one_mul, mul_comm (m.succ⁻¹ : ℝ≥0∞)]

lemma prob_event_uniform_fin_bind_apply_eq_sum (e : set α) :
  ⦃e | $[0..m] >>= oa⦄ = (∑ i, ⦃e | oa i⦄) / m.succ :=
by simp only [prob_event_bind_eq_sum, div_eq_mul_inv, ← finset.sum_mul, one_mul,
  eval_dist_uniform_fin_apply, mul_comm (m.succ⁻¹ : ℝ≥0∞), fin_support_uniform_fin]

end distribution_semantics

end uniform_fin

section uniform_select_vector

/-- Randomly select an element of a vector by using `uniform_of_fin`.
  Again we need to use `succ` for the vectors type to avoid sampling an empty vector -/
@[derive decidable] def uniform_select_vector [decidable_eq α] {n : ℕ} (v : vector α (n + 1)) :
  oracle_comp uniform_selecting α := v.nth <$> $[0..n]

notation `$ᵛ` v := uniform_select_vector v

variables [decidable_eq α] {n : ℕ} (v : vector α (n + 1)) (ob : α → oracle_comp uniform_selecting β) (x : α) (y : β)

section support

@[simp] lemma support_uniform_select_vector : ($ᵛ v).support = {a | a ∈ v.to_list} :=
(support_map v.nth $[0..n]).trans (set.ext (λ a, by simp only [vector.mem_iff_nth,
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

end support

section distribution_semantics

open distribution_semantics

@[simp] lemma eval_dist_uniform_select_vector : ⦃$ᵛ v⦄ = pmf.uniform_of_vector v :=
by rw [uniform_select_vector, pmf.uniform_of_vector_eq_nth_map_uniform_of_fintype,
  eval_dist_map, eval_dist_uniform_fin]

lemma eval_dist_uniform_select_vector_apply : ⦃$ᵛ v⦄ x = v.to_list.count x / n.succ :=
by { rw [eval_dist_uniform_select_vector, pmf.uniform_of_vector_apply], congr }

lemma eval_dist_uniform_select_vector_bind_apply_eq_tsum :
  ⦃($ᵛ v) >>= ob⦄ y = (∑' x, v.to_list.count x * ⦃ob x⦄ y) / n.succ :=
begin
  simp only [eval_dist_bind_apply_eq_tsum, div_eq_mul_inv, ← ennreal.tsum_mul_right,
    eval_dist_uniform_select_vector_apply],
  exact tsum_congr (λ _, by ring),
end

lemma eval_dist_uniform_select_vector_bind_apply_eq_sum :
  ⦃($ᵛ v) >>= ob⦄ y = (∑ x in v.to_list.to_finset, v.to_list.count x * ⦃ob x⦄ y) / n.succ :=
begin
  rw [eval_dist_uniform_select_vector_bind_apply_eq_tsum],
  refine congr_arg (λ x, x / (n.succ : ℝ≥0∞)) (tsum_eq_sum $ λ x hx, _),
  rw [list.count_eq_zero_of_not_mem (λ h, hx $ list.mem_to_finset.2 h), nat.cast_zero, zero_mul],
end

@[simp] lemma prob_event_uniform_select_vector (e : set α) [decidable_pred e] :
  ⦃e | $ᵛ v⦄ = (v.to_list.countp e) / n.succ :=
by { rw [prob_event.def, eval_dist_uniform_select_vector,
  to_outer_measure_uniform_of_vector_apply], congr }

@[simp] lemma prob_event_uniform_select_vector_bind_eq_tsum (e : set β) :
  ⦃e | ($ᵛ v) >>= ob⦄ = (∑' x, (v.to_list.count x) * ⦃e | ob x⦄) / n.succ :=
begin
  simp_rw [prob_event_bind_eq_tsum ($ᵛ v) ob e, eval_dist_uniform_select_vector_apply,
    div_eq_mul_inv, ← ennreal.tsum_mul_right],
  exact tsum_congr (λ _, by ring)
end

lemma prob_event_uniform_select_vector_bind_eq_sum (e : set β) :
  ⦃e | ($ᵛ v) >>= ob⦄ = (∑ x in v.to_list.to_finset, (v.to_list.count x) * ⦃e | ob x⦄) / n.succ :=
begin
  rw [prob_event_uniform_select_vector_bind_eq_tsum],
  refine congr_arg (λ x, x / (n.succ : ℝ≥0∞)) (tsum_eq_sum $ λ x hx, _),
  rw [list.count_eq_zero_of_not_mem (λ h, hx $ list.mem_to_finset.2 h), nat.cast_zero, zero_mul],
end

end distribution_semantics

end uniform_select_vector

section uniform_select_list

/-- If a list isn't empty, we can convert it to a vector and then sample from it.-/
@[derive decidable] def uniform_select_list [decidable_eq α] (xs : list α) (h : ¬ xs.empty) :
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

@[simp] lemma fin_support_uniform_select_list : ($ˡ xs h).fin_support = xs.to_finset :=
(fin_support_eq_iff_support_eq_coe _ _).2 (set.ext $ λ x, by simp only [finset.mem_coe,
  support_uniform_select_list, set.mem_set_of_eq, list.mem_to_finset])

lemma mem_fin_support_uniform_select_list_iff : x ∈ ($ˡ xs h).fin_support ↔ x ∈ xs :=
by rw [fin_support_uniform_select_list, list.mem_to_finset]

end support

section distribution_semantics

open distribution_semantics

lemma eval_dist_uniform_select_list_nil (h : ¬ ([] : list α).empty) (p : pmf α) :
  ⦃$ˡ [] h⦄ = p := false.elim (h rfl)

@[simp] lemma eval_dist_uniform_select_list : ⦃$ˡ xs h⦄ = pmf.uniform_of_list xs h :=
begin
  induction xs with x xs,
  { exact eval_dist_uniform_select_list_nil h _ },
  { simpa only [uniform_select_list_cons, eval_dist_uniform_select_vector] }
end

lemma eval_dist_uniform_select_list_apply : ⦃$ˡ xs h⦄ x = xs.count x / xs.length :=
by { rw [eval_dist_uniform_select_list, pmf.uniform_of_list_apply], congr }

lemma eval_dist_uniform_select_list_bind_apply_eq_tsum :
  ⦃($ˡ xs h) >>= ob⦄ y = (∑' x, xs.count x * ⦃ob x⦄ y) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, eval_dist_uniform_select_vector_bind_apply_eq_tsum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

lemma eval_dist_uniform_select_list_bind_apply_eq_sum :
  ⦃($ˡ xs h) >>= ob⦄ y = (∑ x in xs.to_finset, xs.count x * ⦃ob x⦄ y) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, eval_dist_uniform_select_vector_bind_apply_eq_sum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

@[simp] lemma prob_event_uniform_select_list (e : set α) [decidable_pred e] :
  ⦃e | $ˡ xs h⦄ = xs.countp e / xs.length :=
by { rw [prob_event.def, eval_dist_uniform_select_list,
  to_outer_measure_uniform_of_list_apply], congr }

@[simp] lemma prob_event_uniform_select_list_bind_eq_tsum (e : set β) :
  ⦃e | ($ˡ xs h) >>= ob⦄ = (∑' x, xs.count x * ⦃e | ob x⦄) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_event_uniform_select_vector_bind_eq_tsum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

lemma prob_event_uniform_select_list_bind_eq_sum (e : set β) :
  ⦃e | ($ˡ xs h) >>= ob⦄ = (∑ x in xs.to_finset, xs.count x * ⦃e | ob x⦄) / xs.length :=
begin
  rw [list.empty_iff_eq_nil] at h,
  simp only [uniform_select_list, prob_event_uniform_select_vector_bind_eq_sum,
    vector.to_list_mk, nat.succ_pred_eq_of_pos (list.length_pos_of_ne_nil h)],
end

end distribution_semantics 

end uniform_select_list

section uniform_select_finset

/-- We can sample randomly from a `finset` by converting to a list and then sampling that. -/
@[derive decidable] noncomputable def uniform_select_finset [decidable_eq α]
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

@[simp] lemma fin_support_uniform_select_finset : ($ˢ bag h).fin_support = bag :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_finset]

lemma mem_fin_support_uniform_select_finset_iff : x ∈ ($ˢ bag h).fin_support ↔ x ∈ bag :=
by rw [fin_support_uniform_select_finset]

end support

section distribution_semantics

open distribution_semantics

@[simp] lemma eval_dist_uniform_select_finset : ⦃$ˢ bag h⦄ = pmf.uniform_of_finset bag h :=
by rw [uniform_select_finset, eval_dist_uniform_select_list,
  pmf.uniform_of_finset_eq_uniform_of_list_to_list]

lemma eval_dist_uniform_select_finset_apply : ⦃$ˢ bag h⦄ x = ite (x ∈ bag) bag.card⁻¹ 0 :=
by { rw [eval_dist_uniform_select_finset, pmf.uniform_of_finset_apply], congr }

lemma eval_dist_uniform_select_finset_bind_apply_eq_tsum :
  ⦃$ˢ bag h >>= ob⦄ y = (∑' x, ite (x ∈ bag) (⦃ob x⦄ y) 0) / bag.card :=
by simp only [uniform_select_finset, eval_dist_uniform_select_list_bind_apply_eq_tsum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

lemma eval_dist_uniform_select_finset_bind_apply_eq_sum  :
  ⦃$ˢ bag h >>= ob⦄ y = (∑ x in bag, ⦃ob x⦄ y) / bag.card :=
by simp only [uniform_select_finset, eval_dist_uniform_select_list_bind_apply_eq_sum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

@[simp] lemma prob_event_uniform_select_finset (e : set α) [decidable_pred e] :
  ⦃e | $ˢ bag h⦄ = (bag.filter (∈ e)).card / bag.card :=
by { rw [prob_event.def, eval_dist_uniform_select_finset,
  to_outer_measure_uniform_of_finset_apply], congr }

lemma prob_event_uniform_select_finset_bind_apply_eq_tsum (e : set β) :
  ⦃e | ($ˢ bag h) >>= ob⦄ = (∑' x, ite (x ∈ bag) ⦃e | ob x⦄ 0) / bag.card :=
by simp only [uniform_select_finset, prob_event_uniform_select_list_bind_eq_tsum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

lemma prob_event_uniform_select_finset_bind_apply_eq_sum (e : set β) :
  ⦃e | $ˢ bag h >>= ob⦄ = (∑ x in bag, ⦃e | ob x⦄) / bag.card :=
by simp only [uniform_select_finset, prob_event_uniform_select_list_bind_eq_sum,
  finset.count_to_list, finset.to_list_to_finset, nat.cast_ite, algebra_map.coe_one,
  algebra_map.coe_zero, boole_mul, finset.sum_ite_mem, finset.inter_self, finset.length_to_list]

end distribution_semantics

end uniform_select_finset

section uniform_select_fintype

/-- We can select randomly from a fintyp by using the `finset` corresponding to the `fintype`.
  Again we need to use axiom of choice so this operation is noncomputable. -/
@[derive decidable] noncomputable def uniform_select_fintype (α : Type) [fintype α] [nonempty α]
  [decidable_eq α] : oracle_comp uniform_selecting α :=
uniform_select_finset finset.univ finset.univ_nonempty

notation `$ᵗ` := uniform_select_fintype

variables (α) [fintype α] [nonempty α] [decidable_eq α]
  (ob : α → oracle_comp uniform_selecting β) (x : α) (y : β)

section support

-- TODO: this isn't working properly with `simp`
@[simp] lemma support_uniform_select_fintype : ($ᵗ α).support = ⊤ :=
by rw [uniform_select_fintype, support_uniform_select_finset,
  set.top_eq_univ, finset.coe_eq_univ]

lemma mem_support_uniform_select_fintype : x ∈ ($ᵗ α).support :=
by simp only [support_uniform_select_fintype]

@[simp] lemma fin_support_uniform_select_fintype : ($ᵗ α).fin_support = finset.univ :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_fintype,
  set.top_eq_univ, finset.coe_univ]

lemma mem_fin_support_uniform_select_fintype : x ∈ ($ᵗ α).fin_support :=
by simp only [fin_support_uniform_select_fintype, finset.mem_univ]

end support

section distribution_semantics

open distribution_semantics

@[simp] lemma eval_dist_uniform_select_fintype : ⦃$ᵗ α⦄ = pmf.uniform_of_fintype α :=
by rw [uniform_select_fintype, eval_dist_uniform_select_finset, pmf.uniform_of_fintype]

lemma eval_dist_uniform_select_fintype_apply : ⦃$ᵗ α⦄ x = (fintype.card α)⁻¹ :=
by rw [eval_dist_uniform_select_fintype, pmf.uniform_of_fintype_apply]

lemma eval_dist_uniform_select_fintype_bind_apply_eq_tsum :
  ⦃($ᵗ α) >>= ob⦄ y = (∑' x, ⦃ob x⦄ y) / fintype.card α :=
by simp only [uniform_select_fintype, eval_dist_uniform_select_finset_bind_apply_eq_tsum,
  finset.mem_univ, if_true, finset.card_univ]

lemma eval_dist_uniform_select_fintype_bind_apply_eq_sum :
  ⦃($ᵗ α) >>= ob⦄ y = (∑ x, ⦃ob x⦄ y) / fintype.card α :=
by simp only [uniform_select_fintype, eval_dist_uniform_select_finset_bind_apply_eq_sum,
  finset.mem_univ, if_true, finset.card_univ]

@[simp] lemma prob_event_uniform_select_fintype_apply (e : set α) [decidable_pred e] :
  ⦃e | $ᵗ α⦄ = fintype.card e / fintype.card α :=
by { simp only [prob_event.def, eval_dist_uniform_select_fintype,
  to_outer_measure_uniform_of_fintype_apply, finset.mem_univ, if_true, finset.card_univ], congr }

lemma prob_event_uniform_select_fintype_bind_apply_eq_tsum (e : set β) :
  ⦃e | $ᵗ α >>= ob⦄ = (∑' a, ⦃e | ob a⦄) / fintype.card α :=
by simp only [uniform_select_fintype, prob_event_uniform_select_finset_bind_apply_eq_tsum,
  finset.mem_univ, if_true, finset.card_univ]

lemma prob_event_uniform_select_fintype_apply_bind (e : set β) :
  ⦃e | $ᵗ α >>= ob⦄ = (∑ a, ⦃e | ob a⦄) / fintype.card α :=
by simp only [uniform_select_fintype, prob_event_uniform_select_finset_bind_apply_eq_sum,
  finset.mem_univ, if_true, finset.card_univ]

end distribution_semantics

end uniform_select_fintype

end oracle_comp