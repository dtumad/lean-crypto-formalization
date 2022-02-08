import computational_monads.probabalistic_computation.prob_alg

open_locale classical big_operators nnreal ennreal

variables {A B : Type}

structure prob_comp (A : Type) :=
(alg : prob_alg A)
(wf : alg.well_formed)

namespace prob_comp

section eval_distribution

/-- Private definition used to bootstrap the actual evalution function.
  The reason this is needed is to equate the `pmf` supports with the `prob_comp` supports.
  The use of sigma types also requires lifting the condition from a `Sort` to a `Type`.
   -/
private noncomputable def eval_distribution' :
  Π {A : Type} (ca : prob_alg A) (hca : ca.well_formed), 
    Σ (pa : pmf A), plift (∀ (a : A), (a ∈ pa.support ↔ a ∈ ca.support))
| A (prob_alg.uniform bag) uniform_wf :=
  ⟨pmf.uniform_of_finset bag uniform_wf,
    plift.up $ pmf.mem_support_uniform_of_finset_iff uniform_wf⟩
| _ (prob_alg.bind' A B ca cb) bind_wf :=
  let pa := eval_distribution' ca bind_wf.1 in
  let pb := λ a ha, eval_distribution' (cb a) (bind_wf.2 a ha) in
  ⟨pa.1.bind_on_support $ λ a ha, (pb a $ ((plift.down pa.2) a).1 ha).1,
    plift.up $ λ b, begin
      simp only [pmf.mem_support_bind_on_support_iff, prob_alg.mem_support_bind'_iff, plift.down pa.2],
      split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩; simpa [(plift.down (pb a ha).2) b] using ha'
    end⟩
| A (prob_alg.repeat ca p) repeat_wf :=
  -- let ⟨ca_wf, hp⟩ := repeat_wf in
  let pa := eval_distribution' ca (prob_alg.well_formed_of_repeat_well_formed repeat_wf) in
  let hp : ∃ a ∈ ca.support, p a := prob_alg.exists_mem_support_of_repeat_well_formed repeat_wf in
  ⟨pa.1.filter p (let ⟨a, ha, hap⟩ := hp in ⟨a, hap, (plift.down pa.2 a).2 ha⟩),
    plift.up $ λ a, (pmf.mem_support_filter_iff _ a).trans
      (by rw [plift.down pa.2 a]; exact and_comm (p a) (a ∈ ca.support))⟩

/-- Denotational semantics for evaluation of a `prob_comp A`, as a probability distribution.
  The distribution is given by a probability mass function `pmf A` on the underlying type.
  The well-formed condition ensures the distribution sums to `1` (part of the definition of `pmf`).
  Noncomputability comes from the use of `classical.choice` in defining `ℝ≥0` (and hence `pmf`).
  Computable semantics can be given with some kind of small-step evaluation system. -/
noncomputable def eval_distribution : prob_comp A → pmf A :=
λ ca, (eval_distribution' ca.alg ca.wf).1

@[simp]
theorem support_eval_distribution_eq_support (ca : prob_comp A) :
  (eval_distribution ca).support = ca.alg.support :=
set.ext (plift.down (eval_distribution' ca.alg ca.wf).snd)

lemma mem_support_of_mem_support_eval_distribution {ca : prob_comp A} {a : A}
  (ha : a ∈ ca.eval_distribution.support) : a ∈ ca.alg.support :=
(support_eval_distribution_eq_support ca) ▸ ha

lemma mem_support_eval_distribution_of_mem_support {ca : prob_comp A} {a : A}
  (ha : a ∈ ca.alg.support) : a ∈ ca.eval_distribution.support :=
(support_eval_distribution_eq_support ca).symm ▸ ha

@[simp] lemma eval_distribution_alg_uniform (bag : finset A)
  (h : (prob_alg.uniform bag).well_formed) :
  eval_distribution ⟨prob_alg.uniform bag, h⟩ =
    pmf.uniform_of_finset bag (prob_alg.nonempty_of_uniform_well_formed bag h) :=
rfl

@[simp] lemma eval_distribution_alg_bind' (ca : prob_alg A) (cb : A → prob_alg B)
  (h : (ca >>= cb).well_formed) :
  eval_distribution ⟨ca >>= cb, h⟩ =
    let hca : ca.well_formed := ((prob_alg.bind_well_formed_iff ca cb).1 h).1 in
    (eval_distribution ⟨ca, hca⟩).bind_on_support (λ a ha, 
      let hcb : (cb a).well_formed := ((prob_alg.bind_well_formed_iff ca cb).1 h).2 a
        (mem_support_of_mem_support_eval_distribution ha) in
      eval_distribution ⟨cb a, hcb⟩) :=
by simpa [eval_distribution, eval_distribution']

@[simp] lemma eval_distribution_alg_repeat (ca : prob_alg A) (p : A → Prop)
  (h : (ca.repeat p).well_formed) :
  eval_distribution ⟨ca.repeat p, h⟩ =
    let hca : ca.well_formed := prob_alg.well_formed_of_repeat_well_formed h in
    let hp : ∃ (a : A) (h : set.mem a p), a ∈ (eval_distribution ⟨ca, hca⟩).support :=
      (let ⟨a, ha, hap⟩ := ((prob_alg.repeat_well_formed_iff ca p).1 h).2 in
        ⟨a, hap, mem_support_eval_distribution_of_mem_support ha⟩) in
    (eval_distribution ⟨ca, hca⟩).filter p hp :=
by simp [eval_distribution, eval_distribution']

end eval_distribution

section prob_event

/-- The probability of an event holding on the result of a probablistic computation.
  The definition is in terms of the `outer_measure` structure induced by the `eval_distribution`.
  This is equivalent to the sum of the probabilities of each element of the set. -/
noncomputable def prob_event (ca : prob_comp A) (event : set A) : ℝ≥0 :=
ennreal.to_nnreal (ca.eval_distribution.to_outer_measure event)

-- notation `prob_success` ca := prob_event ca (= tt)

@[simp]
noncomputable def prob_success (ca : prob_comp bool) : ℝ≥0 :=
ca.prob_event (= tt)

end prob_event

end prob_comp