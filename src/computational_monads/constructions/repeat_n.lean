import data.vector.mem

import computational_monads.distribution_semantics.equiv

namespace oracle_comp

open oracle_spec

variables {α : Type} {spec : oracle_spec}
  (oa : oracle_comp spec α) {n : ℕ} (a : α) (as : vector α n)

def repeat_n (oa : oracle_comp spec α) : Π (n : ℕ), oracle_comp spec (vector α n)
| 0 := return vector.nil
| (n + 1) := do { a ← oa, as ← repeat_n n, return (a ::ᵥ as) }

@[simp]
lemma repeat_n_zero : repeat_n oa 0 = return vector.nil := rfl

@[simp]
lemma repeat_n_succ : repeat_n oa (n + 1) =
  do { a ← oa, as ← repeat_n oa n, return (a ::ᵥ as) } := rfl

instance repeat_n.decidable [spec.computable] [hoa : oa.decidable] : (repeat_n oa n).decidable :=
begin
  induction n with n hn,
  { exact oracle_comp.decidable_return vector.nil },
  { haveI : decidable (repeat_n oa n) := hn,
    haveI : decidable_eq α := decidable_eq_of_decidable oa,
    rw [repeat_n_succ],
    apply_instance }
end

section support

@[simp]
lemma support_repeat_n : Π n, support (repeat_n oa n) = { v | ∀ a ∈ v.to_list, a ∈ oa.support }
| 0 := begin
  ext v,
  simp only [repeat_n_zero, support_return, set.mem_singleton_iff,
    eq_iff_true_of_subsingleton, set.mem_set_of_eq, true_iff],
  exact λ a ha, false.elim (v.not_mem_zero a ha),
end
| (n + 1) := begin
  simp_rw [repeat_n, support_bind_bind, support_return],
  ext v,
  simp only [set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  {
    intros a' ha',
    obtain ⟨a, ha, as, has, h⟩ := h,
    rw support_repeat_n n at has,
    rw h at ha',
    rw vector.mem_cons_iff a a' as at ha',
    refine ha'.elim (λ h', _) (λ h', _),
    refine h'.symm ▸ ha,
    exact has a' h'
  },
  {
    obtain ⟨a, as, hv⟩ := vector.exists_eq_cons v,
    refine ⟨a, h a (hv.symm ▸ (vector.mem_cons_self a as)), as, _, hv⟩,
    rw support_repeat_n n,
    refine λ a' ha', h a' (hv.symm ▸ vector.mem_cons_of_mem a a' as ha'),
  }
end

lemma mem_support_repeat_n_iff : as ∈ (repeat_n oa n).support ↔
  ∀ a ∈ as.to_list, a ∈ oa.support := by simp only [support_repeat_n, set.mem_set_of_eq]

lemma support_repeat_n_zero : (repeat_n oa 0).support = ⊤ :=
by simp only [repeat_n_zero, support_return, singleton_eq_top_of_subsingleton]

lemma mem_support_repeat_n_zero (as : vector α 0) : as ∈ (repeat_n oa 0).support :=
by simp only [repeat_n_zero, support_return, singleton_eq_top_of_subsingleton]

@[simp]
lemma support_repeat_n_succ : (repeat_n oa (n + 1)).support =
  {as | as.head ∈ oa.support ∧ as.tail ∈ (repeat_n oa n).support} :=
begin
  refine set.ext (λ as, (mem_support_repeat_n_iff oa _).trans _),
  obtain ⟨a, as', h'⟩ := vector.exists_eq_cons as,
  refine ⟨λ h, _, λ h, _⟩,
  { rw [h', set.mem_set_of_eq, vector.head_cons, vector.tail_cons],
    refine ⟨h a (h'.symm ▸ (vector.mem_cons_self a as')), _⟩,
    rw [mem_support_repeat_n_iff],
    refine λ a' ha', h a' (h'.symm ▸ (vector.mem_cons_of_mem a a' as' ha')) },
  { rw [set.mem_set_of_eq, h', vector.head_cons, vector.tail_cons, mem_support_repeat_n_iff] at h,
    refine λ a' ha', _,
    rw [h', vector.mem_cons_iff] at ha',
    cases ha',
    { exact ha'.symm ▸ h.1 },
    { exact h.2 a' ha' } }
end

@[simp]
lemma mem_support_repeat_n_succ_iff (as : vector α (n + 1)) : as ∈ (repeat_n oa (n + 1)).support ↔
  as.head ∈ oa.support ∧ as.tail ∈ (repeat_n oa n).support :=
by simp only [support_repeat_n_succ, set.mem_set_of_eq]

@[simp]
lemma cons_mem_support_repeat_n_succ_iff : (a ::ᵥ as) ∈ (repeat_n oa (n + 1)).support ↔
  a ∈ oa.support ∧ as ∈ (repeat_n oa n).support :=
by rw [mem_support_repeat_n_succ_iff oa (a ::ᵥ as), vector.head_cons, vector.tail_cons]

lemma mem_support_of_mem_of_support_repeat_n (n : ℕ) (as : vector α n)
  (hv : as ∈ (repeat_n oa n).support) (a : α) (ha : a ∈ as.to_list) : a ∈ oa.support :=
by { rw support_repeat_n at hv, exact hv a ha } 

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

variable [spec.finite_range]

section eval_dist

/-- Probability of a vector is the product of probabilities of each element. -/
@[simp]
lemma eval_dist_repeat_n_apply :
  ⦃repeat_n oa n⦄ as = (as.map (λ a, ⦃oa⦄ a)).to_list.prod :=
begin
  induction n with n hn,
  { simp only [vector.eq_nil as, repeat_n_zero oa, eval_dist_return, pmf.pure_apply,
      if_true, vector.map_nil, vector.to_list_nil, list.prod_nil, eq_self_iff_true] },
  { refine trans (eval_dist_bind_bind_apply _ _ _ _) _,
    simp [hn],
    refine trans (tsum_tsum_eq_single _ as.head as.tail _ _) _,
    { refine λ a h, _,
      simp only [(vector.ne_cons_iff a as as.tail).2 (or.inl $ ne.symm h), if_false] },
    { refine λ a as' h, _,
      simp only [(vector.ne_cons_iff a as as').2 (or.inr $ ne.symm h), if_false] },
    { split_ifs,
      { rw [h, vector.to_list_cons, list.map_cons, list.prod_cons],
        rw [vector.head_cons, vector.tail_cons] },
      { exact false.elim (h $ symm $ vector.cons_head_tail as) } } }
end

end eval_dist

section equiv

end equiv

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end oracle_comp