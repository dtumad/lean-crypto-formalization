import measure_theory.probability_mass_function.constructions
import to_mathlib.general

noncomputable theory

variables {α : Type} --[decidable_eq α]

open_locale classical big_operators nnreal ennreal

lemma sum_fin_succ_eq_sum_fin_add {A : Type} [add_comm_monoid A] {n : ℕ}
  (f : fin (n + 1) → A) :
  ∑ (i : fin (n + 1)), f i = (∑ (i : fin n), f (i + 1)) + f 0 :=
begin
  refine trans (finset.sum_eq_sum_diff_singleton_add (finset.mem_univ 0) _) _,
  congr' 1,
  let g : Π (a : fin (n + 1)), a ∈ (finset.univ \ {0} : finset (fin (n + 1))) → fin n :=
    λ a ha, a.pred (finset.not_mem_singleton.1 (finset.mem_sdiff.1 ha).2),
  exact finset.sum_bij g (λ _ _, finset.mem_univ _) (λ b _, by simp) (λ i j _ _, fin.pred_inj.1)
    (λ b _, ⟨b.succ, finset.mem_sdiff.2 ⟨finset.mem_univ b.succ, (finset.not_mem_singleton.2
      (ne.symm (ne_of_lt $ fin.succ_pos b)))⟩, symm (fin.pred_succ b)⟩),
end

lemma sum_ite_eq_nth {β : Type} [add_comm_monoid_with_one β] 
  (a : α) {n : ℕ} (v : vector α n) :
  ∑ i, ite (v.nth i = a) (1 : β) 0 = ↑(v.to_list.count a) :=
begin
  induction n with n hn,
  { simp [vector.eq_nil v] },
  { obtain ⟨x, xs, hxs⟩ := vector.exists_eq_cons v,
    suffices : (list.count a xs.to_list : β) + ite (x = a) 1 0 =
      ite (x = a) ((list.count a xs.to_list) + 1) (list.count a xs.to_list),
    by simpa only [hxs, sum_fin_succ_eq_sum_fin_add, vector.to_list_cons, list.count_cons,
      vector.nth_cons_zero, @eq_comm _ a, hn xs, fin.coe_eq_cast_succ, fin.coe_succ_eq_succ,
      vector.nth_cons_succ, nat.cast_ite, nat.cast_succ] using this,
    split_ifs,
    { exact rfl },
    { exact add_zero _ } }
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


-- TODO: most have statements could be broken out probably
lemma sum_ite_count {α β : Type*} [add_comm_monoid_with_one β] [topological_space β] [t2_space β]
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

lemma tsum_ite_count {α β : Type*} [add_comm_monoid_with_one β] [topological_space β] [t2_space β]
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
    congr_arg (λ (r : ℝ≥0∞), r / (n + 1)) (tsum_ite_count (∈ t) v.to_list)

@[simp]
lemma to_measure_uniform_of_vector_apply [measurable_space α] (ht : measurable_set t) :
  (uniform_of_vector v).to_measure t = (v.to_list.countp (∈ t)) / (n + 1) :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_vector_apply v t)

end measure

end uniform_of_vector

end pmf