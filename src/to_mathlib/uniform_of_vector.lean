import measure_theory.probability_mass_function.constructions
import to_mathlib.general
import algebra.big_operators.fin

variables {α β : Type}

open_locale classical big_operators nnreal ennreal

lemma sum_ite_eq_nth {β : Type} [add_comm_monoid_with_one β] 
  (a : α) {n : ℕ} (v : vector α n) :
  ∑ i, ite (v.nth i = a) (1 : β) 0 = ↑(v.to_list.count a) :=
begin
  induction n with n hn,
  { simp [vector.eq_nil v] },
  { obtain ⟨x, xs, hxs⟩ := vector.exists_eq_cons v,
    suffices : ite (x = a) 1 0 + (list.count a xs.to_list : β) =
      ite (x = a) ((list.count a xs.to_list) + 1) (list.count a xs.to_list),
    by simpa only [hxs, fin.sum_univ_succ, vector.to_list_cons, list.count_cons,
      vector.nth_cons_zero, @eq_comm _ a, hn xs, fin.coe_eq_cast_succ, fin.coe_succ_eq_succ,
      vector.nth_cons_succ, nat.cast_ite, nat.cast_succ] using this,
    split_ifs,
    { exact add_comm _ _ },
    { exact zero_add _ } }
end

lemma tsum_ite_eq_vector_nth {β : Type} [add_comm_monoid_with_one β] [topological_space β] [t2_space β]
  {n : ℕ} (v : vector α n) (a : α) :
  ∑' (i : fin n), ite (v.nth i = a) (1 : β) 0 = ↑(v.to_list.count a) :=
calc ∑' (i : fin n), ite (v.nth i = a) (1 : β) 0
  = ∑ (i : fin n), ite (v.nth i = a) (1 : β) 0 : tsum_eq_sum (λ _ hb, (hb $ finset.mem_univ _).elim)
  ... = (v.to_list.count a) : (sum_ite_eq_nth a v)

namespace pmf
section uniform_of_vector

variables {n : ℕ} (v : vector α (n + 1)) (a : α)

noncomputable def uniform_of_vector {n : ℕ} (v : vector α (n + 1)) : pmf α :=
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

lemma sum_filter_count_eq_countp (p : α → Prop) (l : list α) :
  ∑ x in l.to_finset.filter p, l.count x = l.countp p :=
begin
  induction l with a as h,
  { simp },
  { rw [list.to_finset_cons],
    by_cases ha : a ∈ as.to_finset,
    { rw [finset.insert_eq_of_mem ha, list.countp_cons],
      calc ∑ x in as.to_finset.filter p, (a :: as).count x
        = ∑ x in as.to_finset.filter p, (as.count x + ite (a = x) (ite (p a) 1 0) 0) :
          begin
            refine finset.sum_congr rfl (λ x hx, _),
            split_ifs with hax hpa,
            { simp [hax] },
            { exact false.elim (hpa $ hax.symm ▸ (finset.mem_filter.1 hx).2) },
            { simp [ne.symm hax] }
          end
        ... = list.countp p as + ite (p a) 1 0 : by simp_rw [finset.sum_add_distrib, h,
          finset.sum_ite_eq, finset.mem_filter, ← ite_and, and_assoc, and_self, ha, true_and] },
    { calc ∑ x in (insert a as.to_finset).filter p, (a :: as).count x
        = (ite (p a) ((a :: as).count a) 0) + ∑ x in as.to_finset.filter p, (a :: as).count x :
          begin
            rw [finset.filter_insert],
            split_ifs with hpa,
            { exact finset.sum_insert (λ h, ha (finset.mem_filter.1 h).1) },
            { exact (zero_add _).symm }
          end
        ... = (ite (p a) 1 0) + ∑ x in as.to_finset.filter p, as.count x : begin
          congr' 1,
          { have : a ∉ as := ha ∘ list.mem_to_finset.2,
            simp [list.count_eq_zero_of_not_mem this] },
          { refine finset.sum_congr rfl (λ x hx, _),
            have : x ≠ a := λ hxa, ha (hxa ▸ (finset.mem_filter.1 hx).1),
            simp [this] }
        end
        ... = (a :: as).countp p : by rw [h, list.countp_cons, add_comm] } }
end

-- TODO: most have statements could be broken out probably
lemma sum_ite_count [add_comm_monoid_with_one β] (p : α → Prop) (l : list α) :
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

lemma tsum_ite_count {α β : Type} [add_comm_monoid_with_one β] [topological_space β] [t2_space β]
  (p : α → Prop) (l : list α) :
  (∑' (x : α), if p x then (l.count x : β) else 0) = l.countp p :=
calc (∑' (x : α), if p x then l.count x else 0 : β)
  = ∑ x in l.to_finset, if p x then l.count x else 0 : begin
    refine tsum_eq_sum (λ a ha, _),
    have : l.count a = 0 := list.count_eq_zero_of_not_mem (λ h, ha (list.mem_to_finset.2 h)),
    simp [this],
  end
  ... = l.countp p : sum_ite_count p l

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
    congr_arg (λ (r : ℝ≥0∞), r / (n + 1)) sorry --(tsum_ite_count (∈ t) v.to_list)

@[simp]
lemma to_measure_uniform_of_vector_apply [measurable_space α] (ht : measurable_set t) :
  (uniform_of_vector v).to_measure t = (v.to_list.countp (∈ t)) / (n + 1) :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_vector_apply v t)

end measure

end uniform_of_vector

end pmf