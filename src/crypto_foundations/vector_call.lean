import crypto_foundations.dist_sem

namespace comp

def vector_call {A : Type} (ca : comp A) : 
  Π n, comp (vector A n)
| 0 := comp.ret vector.nil
| (n + 1) := ca.bind (λ a, (vector_call n).bind (λ as, comp.ret (a ::ᵥ as)))

@[simp]
instance vector_call.is_well_formed {A : Type}
  (ca : comp A) [hca : ca.is_well_formed] (n : ℕ) : (vector_call ca n).is_well_formed :=
begin
  induction n with n hn,
  { simp [vector_call] },
  { simp [vector_call, hn, hca],

   }
end

@[simp]
lemma vector.cons_eq_cons_iff {A : Type} {n : ℕ} (a a' : A) (v v' : vector A n) :
  a ::ᵥ v = a' ::ᵥ v' ↔ a = a' ∧ v = v' :=
⟨λ h, ⟨by simpa using congr_arg vector.head h, by simpa using congr_arg vector.tail h⟩,
  λ h, by rw [h.1, h.2]⟩

theorem eval_distribution_vector_call {A : Type} [decidable_eq A] (ca : comp A) [ca.is_well_formed]
  (n : ℕ) (a : A) (v : vector A n) :
  (vector_call ca (n + 1)).eval_distribution (a ::ᵥ v) = 
    ca.eval_distribution a * (vector_call ca n).eval_distribution v :=
begin
  simp [vector_call],
  refine (tsum_unique _ a _).trans _,
  { refine λ a' ha', mul_eq_zero_of_right _ _,
    refine (tsum_congr (λ v', _)).trans tsum_zero,
    simp [vector.cons_eq_cons_iff, ha'.symm] },
  { congr,
    refine (tsum_unique _ v (λ v' hv', _)).trans (by simp),
    simp [hv'.symm] }
end

@[simp]
theorem mem_support_vector_call_iff {A : Type} [decidable_eq A] 
  (ca : comp A) {n : ℕ} (v : vector A n) : 
  v ∈ (vector_call ca n).support ↔ ∀ (i : fin n), (v.nth i) ∈ ca.support :=
begin
  induction n with n hn,
  { simpa [vector_call] using fin_zero_elim },
  { simp [vector_call],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨a, ha, as, has, hv⟩ := h,
      rw hv,
      have := (hn as).1 has,
      intro i,
      by_cases hi : i = 0,
      { simpa [hi] using ha },
      { rw [← fin.succ_pred i hi, vector.nth_cons_succ a as (i.pred hi)],
        exact this (i.pred hi) } },
    { refine ⟨v.head, _, v.tail, _, _⟩,
      { convert h 0,
        simp only [vector.nth_zero] },
      { rw hn v.tail,
        intro i,
        convert h (i + 1) using 1,
        simp only [fin.coe_eq_cast_succ, fin.coe_succ_eq_succ, vector.nth_tail] },
      { exact v.cons_head_tail.symm } } }
end

end comp
