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

section prod

@[simps]
def prod (ca : prob_comp A) (cb : prob_comp B) :
  prob_comp (A × B) :=
do { a ← ca, b ← cb, return (a, b) }

infix ` ×× `:80 := prod

end prod

section vector_call

@[simp]
def vector_call (ca : prob_comp A) (n : ℕ) : prob_comp (vector A n) :=
vector.m_of_fn (function.const _ ca)

end vector_call

section random

/-- Draw uniformly at random from a finite and nonempty type `A` -/
@[simp]
def random (A : Type) [fintype A] [nonempty A] : prob_comp A :=
uniform finset.univ finset.univ_nonempty

variables (A) [fintype A] [nonempty A]

@[simp] lemma support_random :
  (random A).alg.support = set.univ :=
by simp [random]

end random

end prob_comp