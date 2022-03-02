import computational_monads.probabalistic_computation.monad
import data.bitvec.basic

open_locale classical big_operators nnreal ennreal

variables {A B : Type}

namespace prob_comp

section repeat

@[simps]
def repeat (ca : prob_comp A) (p : A → Prop) (hp : ∃ a ∈ ca.alg.support, p a) : prob_comp A :=
⟨ca.alg.repeat p, prob_alg.repeat_well_formed ca.wf hp⟩

end repeat

section coin

@[simps]
def coin : prob_comp bool := ⟨prob_alg.coin, prob_alg.coin_well_formed⟩

end coin

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

section uniform_fin

lemma t (n : ℕ) : 
  bitvec.to_nat (vector.repeat ff n) = 0 :=
sorry

/-- Generate a random finite integer in the range `[0,1,..,n]`.
  Note that while this function is computable and can be simulated,
    it isn't polynomial time without introducing axioms asserting so. -/
def uniform_fin (n : ℕ) : prob_comp (fin $ n + 1) :=
do {
  (bvec : bitvec (2 ^ n.size)) ← repeat (vector_call coin (2 ^ n.size)) 
    (λ bvec, bitvec.to_nat bvec < n + 1) 
    ⟨vector.repeat ff (2 ^ n.size), by simp, (t $ 2 ^ n.size).symm ▸ nat.zero_lt_succ n⟩,
  return (fin.of_nat' (bitvec.to_nat bvec))
}

notation `$[0...` n `]` := uniform_fin n

@[simp]
lemma support_uniform_fin (n : ℕ) : 
  $[0... n].alg.support = ⊤ :=
sorry

@[simp]
lemma eval_distribution_uniform_fin (n : ℕ) :
  eval_distribution $[0... n] = pmf.uniform_of_fintype (fin $ n + 1) :=
sorry

end uniform_fin

section uniform_select_vector

def uniform_select_vector {n : ℕ} (v : vector A (n + 1)) : prob_comp A := 
(uniform_fin n) >>= (return ∘ v.nth)

notation `$ᵛ` := uniform_select_vector

end uniform_select_vector

section uniform_select_list

def uniform_select_list : Π (l : list A), ¬ l.empty → prob_comp A
| [] h := false.elim (h rfl)
| (x :: xs) _ := uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩

notation `$ˡ` := uniform_select_list

end uniform_select_list

section uniform_select_finset

/-- Noncomputable definition, using choice to order a `finset` and randomly select an element. -/
noncomputable def uniform_select_finset (s : finset A) (hs : s.nonempty) : prob_comp A :=
(uniform_select_list s.to_list (let ⟨x, hx⟩ := hs in 
  λ h, list.not_mem_nil x ((list.empty_iff_eq_nil.1 h) ▸ (finset.mem_to_list s).2 hx)))

@[simp] lemma support_uniform_select_finset (bag : finset A) (h : bag.nonempty) :
  (uniform_select_finset bag h).alg.support = ↑bag := 
sorry

notation `$ˢ` := uniform_select_finset

end uniform_select_finset

section uniform_select_fintype

/-- Draw uniformly at random from a finite and nonempty type `A` -/
noncomputable def uniform_select_fintype (A : Type) [fintype A] [nonempty A] : prob_comp A :=
uniform_select_finset finset.univ finset.univ_nonempty

variables (A) [fintype A] [nonempty A]

@[simp] lemma support_uniform_select_fintype :
  (uniform_select_fintype A).alg.support = set.univ :=
sorry

notation `$ᵗ` := uniform_select_fintype

end uniform_select_fintype

/-- Computable types of uniform random selection -/
example : prob_comp ℕ := do {
  (n₁ : fin 11) ← $[0...10],
  (n₂ : ℕ) ← $ᵛ (1 ::ᵥ (vector.repeat 0 9)),
  (n₃ : ℕ) ← $ˡ [1, 2] (by simp),
  return (n₁ + n₂ + n₃)
}

/-- Noncomputable types of uniform random selection -/
noncomputable example : prob_comp ℕ := do {
  (n₄ : ℕ) ← $ˢ {0, 1, 2} (finset.insert_nonempty _ _),
  (n₅ : fin 100) ← $ᵗ (fin 100),
  return (n₄ + n₅)
}

end prob_comp