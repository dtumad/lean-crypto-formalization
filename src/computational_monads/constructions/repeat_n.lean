import data.vector.basic

import computational_monads.oracle_comp
import computational_monads.distribution_semantics.prob_event

namespace oracle_comp

open oracle_spec

variables {A B : Type} {spec : oracle_spec}
  (oa : oracle_comp spec A) (n : ℕ) (a : A) (as : vector A n)

def repeat_n (oa : oracle_comp spec A) : Π (n : ℕ), oracle_comp spec (vector A n)
| 0 := return vector.nil
| (n + 1) := do { a ← oa, as ← repeat_n n, return (a ::ᵥ as) }

@[simp]
lemma repeat_n_apply_zero : repeat_n oa 0 = return vector.nil := rfl

@[simp]
lemma repeat_n_apply_succ : repeat_n oa (n + 1) =
  do { a ← oa, as ← repeat_n oa n, return (a ::ᵥ as) } := rfl

@[simp]
lemma support_repeat_n : Π n, support (repeat_n oa n) = { v | ∀ a ∈ v.to_list, a ∈ oa.support }
| 0 := begin
  ext v,
  simp only [repeat_n_apply_zero, support_pure, set.mem_singleton_iff,
    eq_iff_true_of_subsingleton, set.mem_set_of_eq, true_iff],
  exact λ a ha, false.elim (vector.not_mem_of_length_zero v a ha),
end
| (n + 1) := begin
  simp_rw [repeat_n, support_bind_bind, support_pure],
  ext v,
  simp only [set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  {
    intros a' ha',
    obtain ⟨a, ha, as, has, h⟩ := h,
    rw support_repeat_n n at has,
    rw h at ha',
    rw vector.mem_cons_iff a as a' at ha',
    refine ha'.elim (λ h', _) (λ h', _),
    refine h'.symm ▸ ha,
    exact has a' h'
  },
  {
    obtain ⟨a, as, hv⟩ := vector.exists_eq_cons v,
    refine ⟨a, h a (hv.symm ▸ vector.mem_cons a as), as, _, hv⟩,
    rw support_repeat_n n,
    refine λ a' ha', h a' (hv.symm ▸ vector.mem_cons_of_mem a as a' ha'),
  }
end

@[simp]
lemma mem_support_repeat_n_iff : as ∈ (repeat_n oa n).support ↔
  ∀ a ∈ as.to_list, a ∈ oa.support := by simp

@[simp]
lemma support_repeat_n_zero : (repeat_n oa 0).support = ⊤ :=
set.ext (λ v, by simp)

@[simp]
lemma mem_support_repeat_n_zero (as : vector A 0) :
  as ∈ (repeat_n oa 0).support := by simp

@[simp]
lemma support_repeat_n_succ : (repeat_n oa (n + 1)).support =
  {v | v.head ∈ oa.support ∧ v.tail ∈ (repeat_n oa n).support} :=
begin
  sorry
end

@[simp]
lemma mem_support_repeat_n_succ_iff (oa : oracle_comp spec A) (v : vector A (n + 1)) :
  v ∈ (repeat_n oa (n + 1)).support ↔ v.head ∈ oa.support ∧ v.tail ∈ (repeat_n oa n).support :=
by { rw [support_repeat_n_succ], exact iff.rfl }

lemma mem_support_of_mem_of_support_repeat_n (oa : oracle_comp spec A) (n : ℕ)
  (v : vector A n) (hv : v ∈ (repeat_n oa n).support) (a : A) (ha : a ∈ v.to_list) :
  a ∈ oa.support :=
by { rw support_repeat_n at hv, exact hv a ha } 

open_locale classical

/-- Probability of a vector is the product of probabilities of each element. -/
@[simp]
lemma eval_distribution_repeat_n_apply [spec.finite_range]
  (oa : oracle_comp spec A) (n : ℕ) (v : vector A n) :
  ⟦repeat_n oa n⟧ v = (v.map (λ a, ⟦oa⟧ a)).to_list.prod :=
begin
  induction n with n hn,
  {
    simp only [vector.eq_nil v, repeat_n_apply_zero oa, eval_distribution_return, pmf.pure_apply,
      if_true, vector.map_nil, vector.to_list_nil, list.prod_nil, eq_self_iff_true],
  },
  {
    rw [repeat_n_apply_succ oa n],
    refine trans (eval_distribution_bind_bind_apply _ _ _ _) _,
    simp [hn],
    refine trans (tsum_tsum_eq_single _ v.head v.tail _) _,
    {
      refine λ a as h, _,
      simp only [(vector.ne_cons_iff v a as).2 h, if_false],
    },
    split_ifs,
    {
      rw [h, vector.to_list_cons, list.map_cons, list.prod_cons],
      rw [vector.head_cons, vector.tail_cons],
    },
    {
      exact false.elim (h $ symm $ vector.cons_head_tail v)
    }
  }
end

end oracle_comp