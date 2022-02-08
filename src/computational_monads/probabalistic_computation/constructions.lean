import computational_monads.probabalistic_computation.prob_comp

open_locale classical big_operators nnreal ennreal

variables {A B : Type}

namespace prob_comp

section bind_on_support

/-- General definition of bind, requiring well-formedness of `(cb a)` for
  only elements `a ∈ ca.alg.support`. Monadic `bind` is defined in terms of this -/
@[simps]
def bind_on_support (ca : prob_comp A) (cb : A → prob_alg B)
  (h : ∀ a ∈ ca.alg.support, (cb a).well_formed) : prob_comp B :=
⟨ca.alg >>= cb, prob_alg.bind_well_formed ca.wf h⟩

@[simp] lemma eval_distribution_bind_on_support (ca : prob_comp A) (cb : A → prob_alg B)
  (h : ∀ a ∈ ca.alg.support, (cb a).well_formed) :
  (bind_on_support ca cb h).eval_distribution =
    ca.eval_distribution.bind_on_support
      (λ a ha, eval_distribution ⟨cb a, h a $ support_eval_distribution_eq_support ca ▸ ha⟩) :=
(eval_distribution_alg_bind' ca.alg cb (ca.bind_on_support cb h).wf)

end bind_on_support

section monad 

@[simps]
instance monad : monad prob_comp :=
{ pure := λ A a, ⟨return a, prob_alg.return_well_formed a⟩,
  bind := λ A B ca cb, ca.bind_on_support (alg ∘ cb) (λ a _, (cb a).wf) }

@[simp] lemma eval_distribution_return (a : A) :
  eval_distribution (return a) = pmf.pure a :=
begin
  show pmf.uniform_of_finset {a} _ = pmf.pure a,
  from pmf.ext (λ a, by simp)
end

lemma eval_distribution_return_apply (a a' : A) :
  eval_distribution (return a) a' = if a' = a then 1 else 0 :=
by simp

@[simp]
lemma eval_distribution_bind (ca : prob_comp A) (cb : A → prob_comp B) :
  eval_distribution (ca >>= cb) = (eval_distribution ca) >>= (eval_distribution ∘ cb) :=
begin
  refine (eval_distribution_bind_on_support ca (alg ∘ cb) _).trans _,
  show ca.eval_distribution.bind_on_support (λ a _, (cb a).eval_distribution) = _,
  from pmf.bind_on_support_eq_bind ca.eval_distribution _,
end

lemma eval_distribution_bind_apply (ca : prob_comp A) (cb : A → prob_comp B) (b : B) :
  eval_distribution (ca >>= cb) b =
    ∑' a, (eval_distribution ca a) * (eval_distribution (cb a) b) :=
(eval_distribution_bind ca cb).symm ▸ pmf.bind_apply ca.eval_distribution _ b

end monad

section uniform

@[simps]
def uniform (bag : finset A) (h : bag.nonempty) : prob_comp A :=
⟨prob_alg.uniform bag, prob_alg.uniform_well_formed h⟩

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

end prob_comp