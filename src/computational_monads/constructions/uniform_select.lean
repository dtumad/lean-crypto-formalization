import computational_monads.distribution_semantics.prob_event

import to_mathlib.uniform_of_vector

namespace oracle_comp

variables {α β γ : Type}

open oracle_spec
open_locale classical

section uniform_fin

/-- Randomly choose a natural `n : ℕ` by querying the uniform selection oracle.
  We implicitly use a `succ` call for the resulting type since `fin 0` is unihabited as a type -/
def uniform_fin (n : ℕ) : oracle_comp uniform_selecting (fin $ n + 1) :=
query n ()

notation `$[0..` n `]` := uniform_fin n

section support

@[simp]
lemma support_uniform_fin (n : ℕ) : support $[0..n] = ⊤ :=
support_query n ()

@[simp]
lemma mem_support_uniform_fin {n : ℕ} (i : fin $ n + 1) : i ∈ support $[0..n] :=
(support_uniform_fin n).symm ▸ set.mem_univ i

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_distribution

@[simp]
lemma eval_distribution_uniform_fin (n : ℕ) : ⦃$[0..n]⦄ = pmf.uniform_of_fintype (fin $ n + 1) :=
rfl

@[simp]
lemma eval_distribution_uniform_fin_apply {n : ℕ} (i : fin $ n + 1) : ⦃$[0..n]⦄ i = 1 / (n + 1) :=
by simp only [eval_distribution_uniform_fin n, pmf.uniform_of_fintype_apply i,
  fintype.card_fin (n + 1), nat.cast_add, nat.cast_one, one_div]

end eval_distribution

section prob_event

@[simp]
lemma prob_event_uniform_fin {n : ℕ} (event : set (fin $ n + 1)) :
  ⦃event | ($[0..n])⦄ = (fintype.card event) / (n + 1) :=
by simp only [uniform_fin, prob_event_query, uniform_selecting.range_apply,
  fintype.card_fin, nat.cast_add, nat.cast_one]

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end uniform_fin

section uniform_select_vector

/-- Randomly select an element of a vector by using `uniform_of_fin`.
  Again we need to use `succ` for the vectors type to avoid sampling an empty vector -/
def uniform_select_vector {n : ℕ} (v : vector α (n + 1)) : oracle_comp uniform_selecting α :=
v.nth <$> $[0..n]

notation `$ᵛ` v := uniform_select_vector v

variables {n : ℕ} (v : vector α (n + 1))

section support

@[simp]
lemma support_uniform_select_vector : support ($ᵛ v) = v.nth '' ⊤ :=
by rw [uniform_select_vector, support_map, support_uniform_fin]

@[simp]
lemma mem_support_uniform_select_vector_iff (a : α) : a ∈ ($ᵛ v).support ↔ a ∈ v.to_list :=
by simp only [vector.mem_iff_nth, support_uniform_select_vector,
  set.top_eq_univ, set.image_univ, set.mem_range]

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_distribution

@[simp]
lemma eval_distribution_uniform_select_vector : ⦃$ᵛ v⦄ = pmf.uniform_of_vector v :=
by simp only [uniform_select_vector, pmf.uniform_of_vector_eq_nth_map_uniform_of_fintype,
  eval_distribution_map, eval_distribution_uniform_fin]

end eval_distribution

section prob_event

end prob_event

section indep_events

end indep_events

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

section support

@[simp]
lemma support_uniform_select_list : Π (xs : list α) (h : ¬ xs.empty),
  support ($ˡ xs h) = {a | a ∈ xs}
| [] h := by simpa only [list.empty, coe_sort_tt, not_true] using h
| (x :: xs) _ := set.ext (λ x', by rw [uniform_select_list,
    mem_support_uniform_select_vector_iff, vector.to_list_mk, set.mem_set_of])

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_distribution

lemma eval_distribution_uniform_select_list_nil (h : ¬ ([] : list α).empty) (p : pmf α) :
  ⦃$ˡ [] h⦄ = p := false.elim (h rfl)

lemma eval_distribution_uniform_select_list : Π (xs : list α) (h : ¬ xs.empty),
  ⦃$ˡ xs h⦄ = pmf.uniform_of_list xs h
| [] h := eval_distribution_uniform_select_list_nil h _
| (x :: xs) h := begin
  rw [uniform_select_list_cons, eval_distribution_uniform_select_vector],
  rw [pmf.uniform_of_vector],
  refl,
end

end eval_distribution

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics 

end uniform_select_list

section uniform_select_finset

/-- We can sample randomly from a `finset` by converting to a list and then sampling that.
  Note this conversion is noncomputable, this conversion uses the axiom of choice. -/
noncomputable def uniform_select_finset (bag : finset α) (h : bag.nonempty) :
  oracle_comp uniform_selecting α := 
uniform_select_list bag.to_list (finset.nonempty.not_empty_to_list h)

notation `$ˢ` := uniform_select_finset

variables (bag : finset α) (h : bag.nonempty)

lemma uniform_select_finset_empty (h : (∅ : finset α).nonempty)
  (oa : oracle_comp uniform_selecting α) : $ˢ ∅ h = oa :=
false.elim (finset.nonempty.ne_empty h rfl)

section support

@[simp]
lemma support_uniform_select_finset : support ($ˢ bag h) = ↑bag :=
by simp only [uniform_select_finset, support_uniform_select_list,
  finset.mem_to_list, finset.set_of_mem]

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_distribution

@[simp]
lemma eval_distribution_uniform_select_finset :
  ⦃$ˢ bag h⦄ = pmf.uniform_of_finset bag h :=
begin
  rw uniform_select_finset,
  rw eval_distribution_uniform_select_list,
  rw pmf.uniform_of_finset_eq_uniform_of_list_to_list,
end

end eval_distribution

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end uniform_select_finset

section uniform_select_fintype

/-- We can select randomly from a fintyp by using the `finset` corresponding to the `fintype`.
  Again we need to use axiom of choice so this operation is noncomputable. -/
noncomputable def uniform_select_fintype (α : Type) [fintype α] [nonempty α] :
  oracle_comp uniform_selecting α :=
uniform_select_finset ⊤ finset.univ_nonempty

notation `$ᵗ` := uniform_select_fintype

variables (α) [fintype α] [nonempty α]

section support

@[simp]
lemma support_uniform_select_fintype :
  support ($ᵗ α) = ⊤ :=
by simpa only [uniform_select_fintype, support_uniform_select_finset,
  set.top_eq_univ, finset.coe_eq_univ]

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_distribution

@[simp]
lemma eval_distribution_uniform_select_fintype :
  ⦃$ᵗ α⦄ = pmf.uniform_of_fintype α :=
sorry

end eval_distribution

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end uniform_select_fintype

end oracle_comp