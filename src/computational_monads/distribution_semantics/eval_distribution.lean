import computational_monads.oracle_comp

open oracle_comp oracle_spec

noncomputable theory

-- Assuming `classical` when working with distributions, as they're already noncomputable
open_locale big_operators nnreal ennreal classical


variables {A B : Type} {spec : oracle_spec} [h' : spec.finite_range]

include h'

section eval_distribution

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

def eval_distribution (oa : oracle_comp spec A) : pmf A :=
(eval_dist oa).1

notation `⟦` oa `⟧` := eval_distribution oa

lemma support_eval_distribution (oa : oracle_comp spec A) :
  ⟦oa⟧.support = oa.support :=
plift.down (eval_dist oa).2

@[simp]
lemma eval_distribution_ge_zero_iff_mem_support (oa : oracle_comp spec A) (a : A) :
  0 ≤ ⟦oa⟧ a ↔ a ∈ oa.support :=
sorry

@[simp]
lemma eval_distribution_eq_zero_iff_not_mem_support (oa : oracle_comp spec A) (a : A) :
  ⟦oa⟧ a = 0 ↔ a ∉ oa.support :=
sorry 

@[simp]
lemma eval_distribution_pure (a : A) :
  ⟦(pure a : oracle_comp spec A)⟧ = pmf.pure a :=
rfl

@[simp]
lemma eval_distribution_return (a : A) :
  ⟦(return a : oracle_comp spec A)⟧ = pmf.pure a :=
rfl

@[simp]
lemma eval_distribution_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) :
  ⟦oa >>= ob⟧ = ⟦oa⟧ >>= λ a, ⟦ob a⟧ := 
by simp [eval_distribution, eval_dist, -bind'_eq_bind, bind]

@[simp]
lemma eval_distibution_pure_bind (a : A) (ob : A → oracle_comp spec B) :
  ⟦return a >>= ob⟧ = ⟦ob a⟧ :=
(eval_distribution_bind (return a) ob).trans (pmf.pure_bind (λ a, ⟦ob a⟧) a)

@[simp]
lemma eval_distribution_map (oa : oracle_comp spec A) (f : A → B) :
  ⟦f <$> oa⟧ = ⟦oa⟧.map f :=
eval_distribution_bind oa (pure ∘ f)

@[simp]
lemma eval_distribution_query (i : spec.ι) (t : spec.domain i) :
  ⟦query i t⟧ = pmf.uniform_of_fintype (spec.range i) :=
rfl

end eval_distribution

section eval_prob

noncomputable def eval_prob (oa : oracle_comp spec A) (event : set A) :
  ℝ≥0∞ := ⟦oa⟧.to_outer_measure event

notation `⟦` event `|` oa `⟧` := eval_prob oa event

noncomputable example (oa : oracle_comp coin_oracle (fin 10)) :
  ℝ≥0∞ := ⟦ (≥) 5 | oa ⟧

@[simp]
lemma eval_prob_eq_zero_iff_disjoint_support (oa : oracle_comp spec A) (event : set A) :
  ⟦ event | oa ⟧ = 0 ↔ disjoint oa.support event :=
sorry

@[simp]
lemma eval_prob_eq_one_iff_support_subset (oa : oracle_comp spec A) (event : set A) :
  ⟦ event | oa ⟧ = 1 ↔ oa.support ⊆ event :=
sorry

@[simp]
lemma eval_prob_return (a : A) (event : set A) :
  ⟦ event | (return a : oracle_comp spec A) ⟧ = if a ∈ event then 1 else 0 :=
pmf.to_outer_measure_pure_apply a event

lemma eval_prob_return_of_true (a : A) (event : set A) (ha : a ∈ event) :
  ⟦ event | (return a : oracle_comp spec A) ⟧ = 1 :=
by simp only [ha, eval_prob_return, if_true]

lemma eval_prob_return_of_false (a : A) (event : set A) (ha : a ∉ event) :
  ⟦ event | (return a : oracle_comp spec A) ⟧ = 0 :=
by simp only [ha, eval_prob_return, if_false]

@[simp]
lemma eval_prob_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (event : set B) :
  ⟦ event | oa >>= ob ⟧ = ∑' (a : A), ⟦oa⟧ a * ⟦ event | ob a ⟧ :=
begin
  simp only [eval_prob, eval_distribution_bind],
  refine pmf.to_outer_measure_bind_apply ⟦oa⟧ (λ a, ⟦ob a⟧) event,
end

@[simp]
lemma eval_prob_pure_bind (a : A) (ob : A → oracle_comp spec B) (event : set B) :
  ⟦ event | return a >>= ob ⟧ = ⟦ event | ob a ⟧ :=
begin
  simp only [eval_prob_bind, eval_distribution_return, pmf.pure_apply],
  refine trans (tsum_congr $ λ a', _) (tsum_ite_eq a ⟦ event | ob a⟧),
  split_ifs with h; simp [h],
end

@[simp]
lemma eval_prop_query (i : spec.ι) (t : spec.domain i) (event : set $ spec.range i) :
  ⟦ event | query i t ⟧ = fintype.card event / fintype.card (spec.range i) :=
pmf.to_outer_measure_uniform_of_fintype_apply event

end eval_prob