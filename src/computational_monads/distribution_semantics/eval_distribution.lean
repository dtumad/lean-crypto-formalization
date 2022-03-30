import computational_monads.oracle_comp

open oracle_comp oracle_spec

variables {A B : Type} {spec : oracle_spec} [h' : spec.finite_range]

include h'

-- Big step semantics for a computation with finite range oracles
-- The result of queries is assumed to be uniform over the oracle's codomain
-- Usually the `spec` when calling this would just be `unit →ₒ bool` (i.e. a tape of random bits),
-- However it can be any more general things as well, e.g. uniform sampling from finite sets
private noncomputable def eval_dist : Π {A : Type} (oa : oracle_comp spec A),
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

noncomputable def eval_distribution (oa : oracle_comp spec A) : pmf A :=
(eval_dist oa).1

notation `⟦` oa `⟧` := eval_distribution oa

lemma support_eval_distribution (oa : oracle_comp spec A) :
  ⟦oa⟧.support = oa.support :=
plift.down (eval_dist oa).2

@[simp]
lemma eval_distribution_pure (a : A) :
  ⟦(pure a : oracle_comp spec A)⟧ = pmf.pure a := rfl

@[simp]
lemma eval_distribution_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) :
  ⟦oa >>= ob⟧ = ⟦oa⟧ >>= λ a, ⟦ob a⟧ := 
by simp [eval_distribution, eval_dist, -bind'_eq_bind, bind]

@[simp]
lemma eval_distribution_query (i : spec.ι) (t : spec.domain i) :
  ⟦query i t⟧ = pmf.uniform_of_fintype (spec.range i) := rfl

@[simp]
lemma eval_distribution_map (oa : oracle_comp spec A) (f : A → B) :
  ⟦f <$> oa⟧ = ⟦oa⟧.map f :=
begin
  sorry,
end