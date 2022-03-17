import computational_monads.probabalistic_computation.oracle_base

open oracle_comp oracle_comp_spec

-- Big step semantics for a computation with finite range oracles
-- The result of queries is assumed to be uniform over the oracle's codomain
-- Usually the `spec` when calling this will just be `unit →ₒ bool` (i.e. a tape of random bits),
-- However it can be any more general things as well, e.g. uniform sampling from finite sets

-- For `repeat oa p`, we filter the distribution by `p`, unless this filters everything,
-- in which case we instead keep the original distribution for `oa`.
-- This represents the limit of the distribution as the number of allowed loops goes to `∞`
private noncomputable def eval_dist {spec : oracle_comp_spec} [spec.computable] [spec.finite_range] :
  Π {A : Type} (oa : oracle_comp spec A),
    Σ (pa : pmf A), plift (pa.support = oa.support)
| _ (pure' A a) := ⟨pmf.pure a, plift.up $ (pmf.support_pure a)⟩
| _ (bind' A B oa ob) := ⟨(eval_dist oa).1 >>= λ a, (eval_dist $ ob a).1, begin
      refine plift.up (set.ext $ λ b, _),
      erw pmf.mem_support_bind_iff,
      simp only [support, plift.down (eval_dist oa).2, set.mem_Union],
      split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩;
        simpa [(plift.down (eval_dist (ob a)).2)] using ha'
  end⟩
| _ (query i t) := ⟨pmf.uniform_of_fintype (spec.range i),
      plift.up ((pmf.support_uniform_of_fintype (spec.range i)))⟩

noncomputable def eval_distribution {A : Type} {spec : oracle_comp_spec}
  [spec.computable] [spec.finite_range] (oa : oracle_comp spec A) : pmf A :=
(eval_dist oa).1

notation `⟦` oa `⟧` := eval_distribution oa

lemma support_eval_distribution {A : Type} {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  (oa : oracle_comp spec A) : ⟦oa⟧.support = oa.support :=
plift.down (eval_dist oa).2

-- TODO: Should this be an actual definition? or is notation easier?
notation oa `≃ₚ` oa' := ⟦oa⟧ = ⟦oa'⟧

@[simp]
lemma bind'_pure'_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A : Type} (ca : oracle_comp spec A) :
  (bind' A A ca (pure' A)) ≃ₚ ca :=
begin
  simp only [eval_distribution, eval_dist],
  exact pmf.bind_pure (eval_dist ca).1,
end

@[simp]
lemma bind_return_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A : Type} (ca : oracle_comp spec A) :
  (ca >>= return) ≃ₚ ca :=
bind'_pure'_equiv ca

@[simp]
lemma pure'_bind'_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A B : Type} (a : A) (cb : A → oracle_comp spec B) :
  (bind' A B (pure' A a) cb) ≃ₚ cb a :=
begin
  simp only [eval_distribution, eval_dist],
  exact pmf.pure_bind (eval_distribution ∘ cb) a,
end

@[simp]
lemma return_bind_equiv {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A B : Type} (a : A) (cb : A → oracle_comp spec B) :
  (return a >>= cb) ≃ₚ cb a :=
pure'_bind'_equiv a cb
