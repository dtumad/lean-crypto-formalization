import computational_monads.probabalistic_computation.prob_comp

open_locale classical big_operators

variables {A B : Type}

namespace prob_comp

section bind_on_support

/-- General definition of bind, requiring well-formedness of `(cb a)` for
  only elements `a ∈ ca.alg.support`. Monadic `bind` is defined in terms of this -/
@[simps]
def bind_on_support (ca : prob_comp A) (cb : A → prob_alg B)
  (h : ∀ a ∈ ca.alg.support, (cb a).well_formed) : prob_comp B :=
⟨ca.alg >>= cb, prob_alg.bind_well_formed ca.wf h⟩

@[simp] lemma support_bind_on_support (ca : prob_comp A) (cb : A → prob_alg B)
  (h : ∀ a ∈ ca.alg.support, (cb a).well_formed) :
  (bind_on_support ca cb h).alg.support = ⋃ a ∈ ca.alg.support, (cb a).support :=
by simp

@[simp] lemma eval_distribution_bind_on_support (ca : prob_comp A) (cb : A → prob_alg B)
  (h : ∀ a ∈ ca.alg.support, (cb a).well_formed) :
  ⟦bind_on_support ca cb h⟧ᵖ =
    ⟦ca⟧ᵖ.bind_on_support (λ a ha, ⟦cb a | h a (support_eval_distribution_eq_support ca ▸ ha)⟧ᵖ) :=
(eval_distribution_alg_bind' ca.alg cb (ca.bind_on_support cb h).wf)

end bind_on_support

section monad 

@[simps]
instance monad : monad prob_comp :=
{ pure := λ A a, ⟨return a, prob_alg.return_well_formed a⟩,
  bind := λ A B ca cb, ca.bind_on_support (alg ∘ cb) (λ a _, (cb a).wf) }

section return

@[simp] lemma support_return (a : A) :
  (return a : prob_comp A).alg.support = {a} := rfl

@[simp] lemma eval_distribution_return (a : A) :
  ⟦return a⟧ᵖ = pmf.pure a := rfl

lemma eval_distribution_return_apply (a a' : A) :
  ⟦return a⟧ᵖ a' = if a' = a then 1 else 0 := rfl

end return

section bind

@[simp] lemma support_bind (ca : prob_comp A) (cb : A → prob_comp B) :
  (ca >>= cb).alg.support = ⋃ a ∈ ca.alg.support, (cb a).alg.support := rfl

@[simp] lemma eval_distribution_bind (ca : prob_comp A) (cb : A → prob_comp B) :
  ⟦ca >>= cb⟧ᵖ = ⟦ca⟧ᵖ >>= (λ a, ⟦cb a⟧ᵖ) :=
begin
  refine (eval_distribution_bind_on_support ca (alg ∘ cb) _).trans _,
  show ⟦ca⟧ᵖ.bind_on_support (λ a _, ⟦cb a⟧ᵖ) = _,
  from pmf.bind_on_support_eq_bind ⟦ca⟧ᵖ _,
end

lemma eval_distribution_bind_apply (ca : prob_comp A) (cb : A → prob_comp B) (b : B) :
  ⟦ca >>= cb⟧ᵖ b = ∑' a, ⟦ca⟧ᵖ a * ⟦cb a⟧ᵖ b :=
(eval_distribution_bind ca cb).symm ▸ pmf.bind_apply ⟦ca⟧ᵖ _ b

end bind

end monad

end prob_comp