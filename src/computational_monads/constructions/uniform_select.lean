import computational_monads.distribution_semantics.prob_event

import to_mathlib.uniform_of_vector

/-!
# Computations Uniformly Drawing From Data Structures

This file defines different uniform computations derived from a `uniform_selecting` oracle.
The base construction is `uniform_fin`, suggestively denoted `$[0..n]`.
From this we build corresponding computations for `vector`, `list`, `finset`, and `fintype`,
  using the notations `$ᵛ`, `$ˡ`, `$ˢ`, and `$ᵗ` respectively.

Note that the `list` and `finset` versions require explicit proofs of being nonempty,
  so using `vector` and `fintype` is preferable when this is possible.
-/

namespace oracle_comp

variables {α β γ : Type}

open oracle_spec
open_locale classical nnreal ennreal

section uniform_fin

/-- Randomly choose a natural `n : ℕ` by querying the uniform selection oracle.
  We implicitly use a `succ` call for the resulting type since `fin 0` is unihabited as a type -/
@[derive decidable]
def uniform_fin (n : ℕ) : oracle_comp uniform_selecting (fin $ n + 1) :=
query n ()

notation `$[0..` n `]` := uniform_fin n

variables (n : ℕ) {m : ℕ} (i : fin $ m + 1)

section support

@[simp]
lemma support_uniform_fin : support $[0..n] = ⊤ := support_query n ()

lemma mem_support_uniform_fin : i ∈ support $[0..m] :=
(support_uniform_fin n).symm ▸ set.mem_univ i

@[simp]
lemma fin_support_uniform_fin : fin_support $[0..n] = ⊤ := fin_support_query n ()

lemma mem_fin_support_uniform_fin : i ∈ fin_support $[0..m] :=
(fin_support_uniform_fin i) ▸ finset.mem_univ i

end support

section distribution_semantics

open distribution_semantics

@[simp]
lemma eval_distribution_uniform_fin : ⦃$[0..n]⦄ = pmf.uniform_of_fintype (fin $ n + 1) := rfl

@[simp]
lemma eval_distribution_uniform_fin_apply : ⦃$[0..m]⦄ i = 1 / (m + 1) :=
by rw [eval_distribution_uniform_fin m, pmf.uniform_of_fintype_apply i,
  fintype.card_fin (m + 1), nat.cast_add, nat.cast_one, one_div]

@[simp]
lemma prob_event_uniform_fin (event : set (fin $ n + 1)) :
  ⦃event | ($[0..n])⦄ = (fintype.card event) / (n + 1) :=
by simp only [uniform_fin, prob_event_query, uniform_selecting.range_apply,
  fintype.card_fin, nat.cast_add, nat.cast_one]

end distribution_semantics

end uniform_fin

section uniform_select_vector

/-- Randomly select an element of a vector by using `uniform_of_fin`.
  Again we need to use `succ` for the vectors type to avoid sampling an empty vector -/
@[derive decidable]
def uniform_select_vector {n : ℕ} (v : vector α (n + 1)) : oracle_comp uniform_selecting α :=
v.nth <$> $[0..n]

notation `$ᵛ` v := uniform_select_vector v

variables {n : ℕ} (v : vector α (n + 1)) (a : α)

section support

@[simp]
lemma support_uniform_select_vector : ($ᵛ v).support = {a | a ∈ v.to_list} :=
(support_map v.nth $[0..n]).trans (set.ext (λ a, by simp only [vector.mem_iff_nth,
  support_uniform_fin, set.top_eq_univ, set.image_univ, set.mem_range, set.mem_set_of_eq]))

lemma mem_support_uniform_select_vector_iff : a ∈ ($ᵛ v).support ↔ a ∈ v.to_list :=
by simp only [support_uniform_select_vector, set.mem_set_of_eq]

@[simp]
lemma fin_support_uniform_select_vector : ($ᵛ v).fin_support = finset.image v.nth finset.univ :=
begin
  rw [fin_support_eq_iff_support_eq_coe, finset.coe_image, support_uniform_select_vector],
  exact set.ext (λ a, by simp only [vector.mem_iff_nth, set.mem_set_of_eq,
    finset.coe_univ, set.image_univ, set.mem_range]), 
end

@[simp]
lemma mem_fin_support_uniform_select_vector_iff : a ∈ ($ᵛ v).fin_support ↔ a ∈ v.to_list :=
by simp only [fin_support_uniform_select_vector, vector.mem_iff_nth,
  finset.mem_image, finset.mem_univ, exists_true_left]

end support

section distribution_semantics

open distribution_semantics

@[simp]
lemma eval_distribution_uniform_select_vector : ⦃$ᵛ v⦄ = pmf.uniform_of_vector v :=
by rw [uniform_select_vector, pmf.uniform_of_vector_eq_nth_map_uniform_of_fintype,
  eval_distribution_map, eval_distribution_uniform_fin]

lemma eval_distribution_uniform_select_vector_apply : ⦃$ᵛ v⦄ a = v.to_list.count a / ↑(n + 1) :=
by rw [eval_distribution_uniform_select_vector, pmf.uniform_of_vector_apply]

@[simp]
lemma prob_event_uniform_select_vector (event : set α) :
  ⦃event | $ᵛ v⦄ = (v.to_list.countp event) / (n + 1) :=
by simp only [prob_event_eq_to_nnreal_to_outer_measure_apply, ennreal.to_nnreal_div,
  eval_distribution_uniform_select_vector, pmf.to_outer_measure_uniform_of_vector_apply,
  ← nat.cast_succ, ennreal.to_nnreal_nat]

end distribution_semantics

end uniform_select_vector

section uniform_select_list

/-- If a list isn't empty, we can convert it to a vector and then sample from it.
  TODO: this should probably correspond to an actual `pmf` function -/
def uniform_select_list : Π (xs : list α) (h : ¬ xs.empty), oracle_comp uniform_selecting α
| [] h := false.elim (h rfl)
| (x :: xs) _ := uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩ 

notation `$ˡ` := uniform_select_list

variables (xs : list α) (x : α) (h : ¬ xs.empty)

lemma uniform_select_list_nil (h : ¬ ([] : list α).empty) (oa : oracle_comp uniform_selecting α) :
  $ˡ [] h = oa := false.elim (h rfl)

lemma uniform_select_list_cons (h : ¬ (x :: xs).empty) :
  $ˡ (x :: xs) h = uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩ := rfl

noncomputable instance uniform_select_list.decidable : ($ˡ xs h).decidable :=
begin
  induction xs with x xs,
  { exact false.elim (h rfl) },
  { exact uniform_select_vector.decidable _ }
end

section support

@[simp]
lemma support_uniform_select_list : ($ˡ xs h).support = {a | a ∈ xs} :=
begin
  induction xs with x xs,
  { simpa only [list.empty, coe_sort_tt, not_true] using h },
  { exact set.ext (λ x', by rw [uniform_select_list,
      mem_support_uniform_select_vector_iff, vector.to_list_mk, set.mem_set_of]) }
end

lemma mem_support_uniform_select_list_iff : x ∈ ($ˡ xs h).support ↔ x ∈ xs :=
by rw [oracle_comp.support_uniform_select_list, set.mem_set_of_eq]

@[simp]
lemma fin_support_uniform_select_list : ($ˡ xs h).fin_support = list.to_finset xs :=
(fin_support_eq_iff_support_eq_coe _ _).2 (set.ext $ λ x, by simp only [finset.mem_coe,
  support_uniform_select_list, set.mem_set_of_eq, list.mem_to_finset])

lemma mem_fin_support_uniform_select_list_iff : x ∈ ($ˡ xs h).fin_support ↔ x ∈ xs :=
by rw [fin_support_uniform_select_list, list.mem_to_finset]

end support

section distribution_semantics

open distribution_semantics

lemma eval_distribution_uniform_select_list_nil (h : ¬ ([] : list α).empty) (p : pmf α) :
  ⦃$ˡ [] h⦄ = p := false.elim (h rfl)

@[simp]
lemma eval_distribution_uniform_select_list : ⦃$ˡ xs h⦄ = pmf.uniform_of_list xs h :=
begin
  induction xs with x xs,
  { exact eval_distribution_uniform_select_list_nil h _ },
  { simpa only [uniform_select_list_cons, eval_distribution_uniform_select_vector] }
end

@[simp]
lemma prob_event_uniform_select_list (event : set α) :
  ⦃event | $ˡ xs h⦄ = xs.countp event / xs.length :=
by simp only [prob_event_eq_to_nnreal_to_outer_measure_apply, ennreal.to_nnreal_div,
  pmf.to_outer_measure_uniform_of_list_apply, ennreal.to_nnreal_nat,
  eval_distribution_uniform_select_list]

end distribution_semantics 

end uniform_select_list

section uniform_select_finset

/-- We can sample randomly from a `finset` by converting to a list and then sampling that.
  Note this conversion is noncomputable, this conversion uses the axiom of choice. -/
@[derive decidable]
noncomputable def uniform_select_finset (bag : finset α) (h : bag.nonempty) :
  oracle_comp uniform_selecting α := 
uniform_select_list bag.to_list (finset.nonempty.not_empty_to_list h)

notation `$ˢ` := uniform_select_finset

variables (bag : finset α) (h : bag.nonempty) (a : α)

lemma uniform_select_finset_empty (h : (∅ : finset α).nonempty)
  (oa : oracle_comp uniform_selecting α) : $ˢ ∅ h = oa :=
false.elim (finset.nonempty.ne_empty h rfl)

section support

@[simp]
lemma support_uniform_select_finset : ($ˢ bag h).support = ↑bag :=
by simp only [uniform_select_finset, support_uniform_select_list,
  finset.mem_to_list, finset.set_of_mem]

lemma mem_support_uniform_select_finset_iff : a ∈ ($ˢ bag h).support ↔ a ∈ bag :=
by rw [support_uniform_select_finset, finset.mem_coe]

@[simp]
lemma fin_support_uniform_select_finset : ($ˢ bag h).fin_support = bag :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_finset]

lemma mem_fin_support_uniform_select_finset_iff : a ∈ ($ˢ bag h).fin_support ↔ a ∈ bag :=
by rw [fin_support_uniform_select_finset]

end support

section distribution_semantics

open distribution_semantics

@[simp]
lemma eval_distribution_uniform_select_finset : ⦃$ˢ bag h⦄ = pmf.uniform_of_finset bag h :=
by rw [uniform_select_finset, eval_distribution_uniform_select_list,
  pmf.uniform_of_finset_eq_uniform_of_list_to_list]

lemma eval_distribution_uniform_select_finset_apply :
  ⦃$ˢ bag h⦄ a = if a ∈ bag then bag.card⁻¹ else 0 :=
by rw [eval_distribution_uniform_select_finset, pmf.uniform_of_finset_apply]

@[simp]
lemma prob_event_uniform_select_finset (event : set α) :
  ⦃event | $ˢ bag h⦄ = (bag.filter (∈ event)).card / bag.card :=
by simp only [prob_event_eq_to_nnreal_to_outer_measure_apply, ennreal.to_nnreal_div,
  ennreal.to_nnreal_nat, eval_distribution_uniform_select_finset,
  pmf.to_outer_measure_uniform_of_finset_apply]

end distribution_semantics

end uniform_select_finset

section uniform_select_fintype

/-- We can select randomly from a fintyp by using the `finset` corresponding to the `fintype`.
  Again we need to use axiom of choice so this operation is noncomputable. -/
@[derive decidable]
noncomputable def uniform_select_fintype (α : Type) [fintype α] [nonempty α] :
  oracle_comp uniform_selecting α :=
uniform_select_finset finset.univ finset.univ_nonempty

notation `$ᵗ` := uniform_select_fintype

variables (α) [fintype α] [nonempty α] (a : α)

section support

@[simp]
lemma support_uniform_select_fintype : ($ᵗ α).support = ⊤ :=
by rw [uniform_select_fintype, support_uniform_select_finset,
  set.top_eq_univ, finset.coe_eq_univ]

lemma mem_support_uniform_select_fintype : a ∈ ($ᵗ α).support :=
by simp only [support_uniform_select_fintype]

@[simp]
lemma fin_support_uniform_select_fintype : ($ᵗ α).fin_support = finset.univ :=
by rw [fin_support_eq_iff_support_eq_coe, support_uniform_select_fintype,
  set.top_eq_univ, finset.coe_univ]

lemma mem_fin_support_uniform_select_fintype : a ∈ ($ᵗ α).fin_support :=
by simp only [fin_support_uniform_select_fintype, finset.mem_univ]

end support

section distribution_semantics

open distribution_semantics

@[simp]
lemma eval_distribution_uniform_select_fintype : ⦃$ᵗ α⦄ = pmf.uniform_of_fintype α :=
by rw [uniform_select_fintype, eval_distribution_uniform_select_finset, pmf.uniform_of_fintype]

lemma eval_distribution_uniform_select_fintype_apply : ⦃$ᵗ α⦄ a = (fintype.card α)⁻¹ :=
by rw [eval_distribution_uniform_select_fintype, pmf.uniform_of_fintype_apply]

@[simp]
lemma prob_event_uniform_select_fintype_apply (event : set α) :
  ⦃event | $ᵗ α⦄ = fintype.card event / fintype.card α :=
by simp only [prob_event_eq_to_nnreal_to_outer_measure_apply, ennreal.to_nnreal_div,
  ennreal.to_nnreal_nat, eval_distribution_uniform_select_fintype,
  pmf.to_outer_measure_uniform_of_fintype_apply]

end distribution_semantics

end uniform_select_fintype

end oracle_comp