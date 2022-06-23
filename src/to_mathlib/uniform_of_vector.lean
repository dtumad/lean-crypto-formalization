import measure_theory.probability_mass_function.constructions

noncomputable theory

variables {α : Type} --[decidable_eq α]

open_locale classical big_operators nnreal ennreal

lemma vector.to_list_nonempty {n : ℕ} (v : vector α (n + 1)) : ¬ v.to_list.empty :=
match v with | ⟨a :: as, _⟩ := by simp end

def pmf.uniform_of_vector {n : ℕ} (v : vector α (n + 1)) : pmf α :=
pmf.of_multiset (quotient.mk v.to_list)
(by simpa only [multiset.quot_mk_to_coe, ne.def, multiset.coe_eq_zero, ← list.empty_iff_eq_nil]
  using vector.to_list_nonempty v)

@[simp]
lemma pmf.uniform_of_vector_apply {n : ℕ} (v : vector α (n + 1)) (a : α) :
  (pmf.uniform_of_vector v) a = (list.count a v.to_list) / v.to_list.length :=
by simp only [pmf.uniform_of_vector, pmf.of_multiset_apply,
  multiset.quot_mk_to_coe, multiset.coe_count, multiset.coe_card]

lemma tsum_ite_eq_vector_nth_eq_count {n : ℕ} (v : vector α n) (a : α) :
  ∑' (i : fin n), ite (a = v.nth i) 1 0 = v.to_list.count a :=
begin
  sorry
end

@[simp]
lemma nat.cast_tsum {α β : Type*} [add_comm_monoid β] [has_one β] [topological_space β] (f : α → ℕ) :
  ↑(∑' (a : α), f a) = ∑' (a : α), (f a : β) :=
begin
  sorry
end

lemma tsum_ite_eq_vector_nth {n : ℕ} (v : vector α n) (a : α) (x : ℝ≥0) :
  ∑' (i : fin n), ite (a = v.nth i) x 0 = x * (v.to_list.count a) :=
calc ∑' (i : fin n), ite (a = v.nth i) x 0
  = ∑' (i : fin n), x * (ite (a = v.nth i) 1 0) : tsum_congr (λ i, symm $ mul_boole _ x)
  ... = x * ∑' (i : fin n), ite (a = v.nth i) 1 0 : nnreal.tsum_mul_left x _
  ... = x * (v.to_list.count a) : begin
    refine congr_arg ((*) x) _,
    refine trans _ (congr_arg coe $ tsum_ite_eq_vector_nth_eq_count v a),
    simp only [nat.cast_tsum, nat.cast_ite, nat.cast_one, nat.cast_zero]
  end