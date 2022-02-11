import computational_monads.probabalistic_computation.monad

open_locale classical big_operators nnreal ennreal

variables {A B : Type}

namespace prob_comp

section uniform

@[simps]
def uniform (bag : finset A) (h : bag.nonempty) : prob_comp A :=
⟨prob_alg.uniform bag, prob_alg.uniform_well_formed h⟩

@[simp] lemma support_uniform (bag : finset A) (h : bag.nonempty) :
  (uniform bag h).alg.support = ↑bag :=
by simp

@[simp] lemma eval_distribution_uniform (bag : finset A) (h : bag.nonempty) :
  eval_distribution (uniform bag h) = pmf.uniform_of_finset bag h :=
rfl

lemma eval_distribution_uniform_apply (bag : finset A) (h : bag.nonempty) (a : A) :
  eval_distribution (uniform bag h) a = if a ∈ bag then (bag.card : ℝ≥0)⁻¹ else 0 :=
by exact pmf.uniform_of_finset_apply h a

end uniform

section repeat

@[simps]
def repeat (ca : prob_comp A) (p : A → Prop) (hp : ∃ a ∈ ca.alg.support, p a) : prob_comp A :=
⟨ca.alg.repeat p, prob_alg.repeat_well_formed ca.wf hp⟩

end repeat

section prod_call

def prod_call (ca : prob_comp A) (cb : prob_comp B) :
  prob_comp (A × B) :=
do { a ← ca, b ← cb, return (a, b) }

infix ` ×× `:80 := prod_call

@[simp] lemma support_prod_call (ca : prob_comp A) (cb : prob_comp B) :
  (ca ×× cb).alg.support = ca.alg.support ×ˢ cb.alg.support :=
begin
  ext x,
  simp only [prod_call, support_bind, support_return, set.mem_Union, set.mem_singleton_iff],
  refine ⟨λ h, let ⟨a, ha, b, hb, h'⟩ := h in h'.symm ▸ ⟨ha, hb⟩,
    λ h, ⟨x.1, h.1, x.2, h.2, prod.mk.eta.symm⟩⟩,
end

end prod_call

section vector_call

def vector_call (ca : prob_comp A) (n : ℕ) : prob_comp (vector A n) :=
vector.m_of_fn (function.const (fin n) ca)

@[simp] lemma vector_call_zero (ca : prob_comp A) :
  ca.vector_call 0 = return vector.nil :=
by simp [vector_call, vector.m_of_fn]

@[simp] lemma vector_call_succ (ca : prob_comp A) (n : ℕ) :
  ca.vector_call n.succ = do{ a ← ca, v ← ca.vector_call n, return (a ::ᵥ v) } :=
by simp [vector_call, vector.m_of_fn]

@[simp] lemma support_vector_call (ca : prob_comp A) (n : ℕ) :
  (ca.vector_call n).alg.support = {v | ∀ (i : fin n), v.nth i ∈ ca.alg.support} :=
begin
  induction n with n hn,
  { refine set.ext (λ v, _),
    rw [vector_call_zero, support_return, set.mem_singleton_iff,
      eq_iff_true_of_subsingleton v, true_iff],
    refine fin_zero_elim },
  { refine set.ext (λ v, _),
    simp_rw [vector_call_succ, support_bind, set.mem_Union,
      support_return, set.mem_singleton_iff],
    refine ⟨λ h i, _, λ h, _⟩,
    { obtain ⟨a, ha, v', hv', rfl⟩ := h,
      rw [hn] at hv',
      refine fin.induction_on i (by simp [ha]) (λ i _, by simp [hv' i]) },
    { refine ⟨v.head, v.nth_zero ▸ h 0, v.tail, _, v.cons_head_tail.symm⟩,
      exact hn.symm ▸ λ i, (v.nth_tail_succ i).symm ▸ h i.succ } }
end

end vector_call

section random

/-- Draw uniformly at random from a finite and nonempty type `A` -/
def random (A : Type) [fintype A] [nonempty A] : prob_comp A :=
uniform finset.univ finset.univ_nonempty

variables (A) [fintype A] [nonempty A]

@[simp] lemma support_random :
  (random A).alg.support = set.univ :=
by simp [random]

end random

end prob_comp