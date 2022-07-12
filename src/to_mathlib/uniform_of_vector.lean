import measure_theory.probability_mass_function.constructions
import to_mathlib.general

noncomputable theory

variables {α : Type} --[decidable_eq α]

open_locale classical big_operators nnreal ennreal

lemma vector.to_list_nonempty {n : ℕ} (v : vector α (n + 1)) : ¬ v.to_list.empty :=
match v with
| ⟨a :: as, _⟩ := by simp
end


-- TODO: most have statements could be broken out probably
lemma sum_ite_count {α β : Type*} [add_comm_monoid β] [has_one β] [topological_space β] [t2_space β]
  (p : α → Prop) (l : list α) :
  (∑ x in l.to_finset, if p x then (l.count x : β) else 0) = l.countp p :=
begin
  induction l with a as h,
  { simp },
  { rw [list.countp_cons, nat.cast_add, ← h],
    have : a ∈ (a :: as).to_finset := list.mem_to_finset.2 (list.mem_cons_self a as),
    rw [finset.sum_eq_sum_diff_singleton_add this _],
    by_cases ha : a ∈ as.to_finset,
    { have : (a :: as).to_finset = as.to_finset :=
        by rw [list.to_finset_cons, finset.insert_eq_of_mem ha],
      simp_rw [this, finset.sum_eq_sum_diff_singleton_add ha _, add_assoc],
      congr' 1,
      { refine finset.sum_congr rfl (λ x hx, _),
        rw [finset.mem_sdiff, finset.not_mem_singleton, ne.def] at hx,
        have : list.count x (a :: as) = list.count x as := by simp [hx],
        rw this },
      { split_ifs; simp } },
    { have : (a :: as).to_finset \ {a} = as.to_finset := begin
        rw [list.to_finset_cons, finset.insert_sdiff_of_mem _ (finset.mem_singleton_self a)],
        rw [finset.sdiff_singleton_not_mem_eq_self as.to_finset ha],
      end,
      simp_rw [this],
      congr' 1,
      { refine finset.sum_congr rfl (λ x hx, _),
        have : list.count x (a :: as) = list.count x as :=
          list.count_cons_of_ne (λ hxa, ha (hxa ▸ hx)) as,
        rw this },
      { have : a ∉ as := ha ∘ (list.mem_to_finset.2),
        have : list.count a (a :: as) = 1 :=
          by simp [list.count_cons, list.count_eq_zero_of_not_mem this],
        simp [this] } } }
end

lemma tsum_ite_count {α β : Type*} [add_comm_monoid β] [has_one β] [topological_space β] [t2_space β]
  (p : α → Prop) (l : list α) :
  (∑' (x : α), if p x then (l.count x : β) else 0) = l.countp p :=
calc (∑' (x : α), if p x then l.count x else 0 : β)
  = ∑ x in l.to_finset, if p x then l.count x else 0 : begin
    refine tsum_eq_sum (λ a ha, _),
    have : l.count a = 0 := list.count_eq_zero_of_not_mem (λ h, ha (list.mem_to_finset.2 h)),
    simp [this],
  end
  ... = l.countp p : sum_ite_count p l

lemma sum_fin_succ_diff_eq_sum_fin {A : Type} [add_comm_monoid A] {n : ℕ}
  (f : fin (n + 1) → A) :
  ∑ i in (finset.univ \ {↑n + 1} : finset (fin $ n + 1)), f i
    = ∑ (i : fin n), f i :=
sorry

lemma sum_fin_succ_eq_sum_fin {A : Type} [add_comm_monoid A] {n : ℕ}
  (f : fin (n + 1) → A) :
  ∑ (i : fin (n + 1)), f i = (∑ (i : fin n), f i) + f (n + 1) :=
begin
  have : (n + 1 : fin (n + 1)) ∈ finset.univ := finset.mem_univ _,
  refine trans (finset.sum_eq_sum_diff_singleton_add this f) _,
  refine congr_arg (λ x, x + f (n + 1)) _,
  exact sum_fin_succ_diff_eq_sum_fin f
end

lemma sum_ite_eq_nth (a : α) : Π {n : ℕ} (v : vector α n),
  ∑ i, (if (v.nth i = a) then 1 else 0) = v.to_list.count a
| 0 ⟨[], h⟩ := by simp [finset.filter_eq_empty_iff]
| (n + 1) ⟨x :: xs, h⟩ := begin
  rw [vector.to_list, list.count_cons],
  split_ifs,
  {
    sorry
  },
  {
    sorry
  }
end

lemma tsum_ite_eq_nth {n : ℕ} (v : vector α n) (a : α) :
  ∑' (i : fin n), ite (v.nth i = a) 1 0 = v.to_list.count a :=
calc ∑' (i : fin n), ite (v.nth i = a) 1 0
  = ∑ i, if (v.nth i = a) then 1 else 0 : begin
    sorry
  end
  ... = v.to_list.count a : sum_ite_eq_nth a v

lemma tsum_ite_eq_vector_nth {n : ℕ} (v : vector α n) (a : α) (x : ℝ≥0) :
  ∑' (i : fin n), ite (v.nth i = a) x 0 = x * (v.to_list.count a) :=
calc ∑' (i : fin n), ite (v.nth i = a) x 0
  = ∑' (i : fin n), x * (ite (v.nth i = a) 1 0) : tsum_congr (λ i, symm $ mul_boole _ x)
  ... = x * ∑' (i : fin n), ite (v.nth i = a) 1 0 : nnreal.tsum_mul_left x _
  ... = x * (v.to_list.count a) : begin
    refine congr_arg ((*) x) _,
    refine trans _ (congr_arg coe $ tsum_ite_eq_nth v a),
    simp only [nat.cast_tsum, nat.cast_ite, nat.cast_one, nat.cast_zero]
  end



namespace pmf
section uniform_of_vector

variables {n : ℕ} (v : vector α (n + 1)) (a : α)

def uniform_of_vector {n : ℕ} (v : vector α (n + 1)) : pmf α :=
of_multiset (quotient.mk v.to_list) (by simpa only [multiset.quot_mk_to_coe,
  ne.def, multiset.coe_eq_zero, ← list.empty_iff_eq_nil] using vector.to_list_nonempty v)

@[simp] lemma uniform_of_vector_apply :
  (uniform_of_vector v) a = (list.count a v.to_list) / (n + 1) :=
by simp [uniform_of_vector]

@[simp] lemma uniform_of_vector_apply_eq_zero_iff : (uniform_of_vector v) a = 0 ↔ a ∉ v.to_list :=
by simp [list.count_eq_zero]

@[simp] lemma uniform_of_vector_apply_ne_zero_iff : (uniform_of_vector v) a ≠ 0 ↔ a ∈ v.to_list :=
by rw [ne.def, uniform_of_vector_apply_eq_zero_iff, not_not]

@[simp] lemma support_uniform_of_vector : (uniform_of_vector v).support = {a | a ∈ v.to_list} :=
set.ext (λ a, by rw [mem_support_iff, uniform_of_vector_apply_ne_zero_iff, set.mem_set_of_eq])

lemma mem_support_uniform_of_vector_iff :
  a ∈ (uniform_of_vector v).support ↔ a ∈ v.to_list :=
by rw [support_uniform_of_vector, set.mem_set_of_eq]

section measure

variable (t : set α)

@[simp]
lemma to_outer_measure_uniform_of_vector_apply : (uniform_of_vector v).to_outer_measure t =
  (v.to_list.countp (∈ t)) / (n + 1) :=
calc (uniform_of_vector v).to_outer_measure t
  = ∑' (x : α), t.indicator (λ a, (v.to_list.count a) / (n + 1)) x :
    by simp [to_outer_measure_apply, set.indicator_apply]
  ... = ∑' (x : α), (t.indicator (λ a, v.to_list.count a) x) / (n + 1) :
    by simp only [div_eq_mul_inv, set.indicator_mul_left]
  ... = (∑' (x : α), t.indicator (λ a, v.to_list.count a) x) / (n + 1) :
    by simp only [div_eq_mul_inv, ennreal.tsum_mul_right]
  ... = (v.to_list.countp (∈ t)) / (n + 1) :
    congr_arg (λ (r : ℝ≥0∞), r / (n + 1)) (tsum_ite_count (∈ t) v.to_list)

@[simp]
lemma to_measure_uniform_of_vector_apply [measurable_space α] (ht : measurable_set t) :
  (uniform_of_vector v).to_measure t = (v.to_list.countp (∈ t)) / (n + 1) :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_vector_apply v t)

end measure

end uniform_of_vector

end pmf