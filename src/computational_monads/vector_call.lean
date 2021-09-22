import computational_monads.dist_sem
import computational_complexity.complexity_class

namespace comp

-- TODO: This might be a better definition for computational complexity proofs
def vector_call {A : Type} (ca : comp A) (n : ℕ) :
  comp (vector A n) :=
vector.m_of_fn (function.const _ ca)

variables {A : Type} (ca : comp A)

@[simp]
lemma vector_call_zero : 
  (vector_call ca 0) = return vector.nil :=
rfl

@[simp]
lemma vector_call_succ {n : ℕ} :
  (vector_call ca n.succ) =
    do { a ← ca, as ← vector_call ca n, return (a ::ᵥ as) } :=
by simp [vector_call, vector.m_of_fn]

@[simp]
instance vector_call.is_well_formed
  [hca : ca.is_well_formed] (n : ℕ) :
  (vector_call ca n).is_well_formed :=
begin
  induction n with n hn,
  { simp },
  { simp [hn] }
end

@[simp]
lemma mem_support_vector_call_iff {A : Type}
  (ca : comp A) {n : ℕ} (as : vector A n) :
  as ∈ (vector_call ca n).support ↔
    ∀ (i : fin n), (as.nth i) ∈ ca.support :=
begin
  induction n with n hn,
  { simpa using fin_zero_elim },
  { simp,
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨a, ha, as, has, h⟩ := h,
      rw [h],
      refine λ i, if hi : i = 0 then _ else _,
      { simpa [hi] using ha },
      { rw [← fin.succ_pred i hi, vector.nth_cons_succ a as (i.pred hi)],
        exact (hn as).1 has (i.pred hi) } },
    { refine ⟨as.head, vector.nth_zero as ▸ h 0, as.tail,
        (hn as.tail).2 (λ i, (vector.nth_tail as i).symm ▸ h _),
        symm $ vector.cons_head_tail as⟩ } }
end

@[simp]
theorem eval_distribution_vector_call_succ {A : Type} [decidable_eq A] (ca : comp A) [ca.is_well_formed]
  (n : ℕ) (a : A) (as : vector A n) :
  (vector_call ca (n + 1)).eval_distribution (a ::ᵥ as) = 
    ca.eval_distribution a * (vector_call ca n).eval_distribution as :=
begin
  simp only [mul_boole, return_eq, pmf.pure_apply, eval_distribution_ret, pmf.bind_apply, vector_call_succ,
    eval_distribution_bind_bind, vector.cons_eq_cons_iff],
  refine trans (tsum_eq_single a (λ a' ha', _)) (trans (tsum_eq_single as (λ as' has', _)) _),
  { simp only [ne.symm ha', tsum_zero, if_false, false_and] },
  { simp only [ne.symm has', if_false, and_false] },
  { simp only [if_true, eq_self_iff_true, and_self] }
end

end comp
