import computational_monads.oracle_comp
import to_mathlib.general

noncomputable theory

open oracle_comp oracle_spec
open_locale big_operators nnreal ennreal classical

-- Big step semantics for a computation with finite range oracles
-- The result of queries is assumed to be uniform over the oracle's codomain
-- Usually the `spec` when calling this would just be `unit →ₒ bool` (i.e. a tape of random bits),
-- However it can be any more general things as well, e.g. uniform sampling from finite sets
private noncomputable def eval_dist {spec : oracle_spec} [h' : spec.finite_range] :
  Π {A : Type} (oa : oracle_comp spec A), Σ (pa : pmf A), plift (pa.support = oa.support)
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

variables {A B C : Type} {spec : oracle_spec} [h' : spec.finite_range]
include h'

def eval_distribution (oa : oracle_comp spec A) : pmf A :=
(eval_dist oa).1

-- TODO : maybe ⦃ oa ⦄ is better to avoid double overloading?
notation `⟦` oa `⟧` := eval_distribution oa

@[simp]
lemma eval_distribution_pure (a : A) :
  ⟦(pure a : oracle_comp spec A)⟧ = pmf.pure a :=
rfl

@[simp]
lemma eval_distribution_pure_apply (a a' : A) :
  ⟦(pure a : oracle_comp spec A)⟧ a' = if a' = a then 1 else 0 :=
by convert (pmf.pure_apply a a')

@[simp]
lemma eval_distribution_return (a : A) :
  ⟦(return a : oracle_comp spec A)⟧ = pmf.pure a :=
rfl

@[simp]
lemma eval_distribution_return_apply (a a' : A) :
  ⟦(return a : oracle_comp spec A)⟧ a' = if a' = a then 1 else 0 :=
eval_distribution_pure_apply a a'

@[simp]
lemma eval_distribution_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) :
  ⟦oa >>= ob⟧ = ⟦oa⟧ >>= λ a, ⟦ob a⟧ := 
by simp [eval_distribution, eval_dist, -bind'_eq_bind, bind]

@[simp]
lemma eval_distribution_bind_apply (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (b : B) :
  ⟦oa >>= ob⟧ b = ∑' (a : A), ⟦oa⟧ a * ⟦ob a⟧ b :=
by simpa only [eval_distribution_bind]

@[simp]
lemma eval_distribution_bind_bind_apply (oa : oracle_comp spec A)
  (ob : A → oracle_comp spec B) (oc : A → B → oracle_comp spec C) (c : C) :
  ⟦do {a ← oa, b ← ob a, oc a b}⟧ c = ∑' (a : A) (b : B), ⟦oa⟧ a * (⟦ob a⟧ b * ⟦oc a b⟧ c) :=
(eval_distribution_bind_apply oa _ c).trans
  (tsum_congr $ λ a, by simp only [eval_distribution_bind_apply, nnreal.tsum_mul_left (⟦oa⟧ a)])

@[simp]
lemma eval_distribution_map (oa : oracle_comp spec A) (f : A → B) :
  ⟦f <$> oa⟧ = ⟦oa⟧.map f :=
eval_distribution_bind oa (pure ∘ f)

@[simp]
lemma eval_distribution_map_apply (oa : oracle_comp spec A) (f : A → B) (b : B) :
  ⟦f <$> oa⟧ b = ∑' (a : A), if f a = b then ⟦oa⟧ a else 0 :=
by simp only [eval_distribution_map oa f, pmf.map_apply f ⟦oa⟧, @eq_comm B b]

@[simp]
lemma eval_distribution_query (i : spec.ι) (t : spec.domain i) :
  ⟦query i t⟧ = pmf.uniform_of_fintype (spec.range i) :=
rfl

@[simp]
lemma eval_distribution_query_apply (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  ⟦query i t⟧ u = 1 / (fintype.card $ spec.range i) :=
by simp only [eval_distribution_query, pmf.uniform_of_fintype_apply, one_div]

section support

@[simp]
lemma support_eval_distribution (oa : oracle_comp spec A) :
  ⟦oa⟧.support = oa.support :=
plift.down (eval_dist oa).2

@[simp]
lemma eval_distribution_eq_zero_iff_not_mem_support (oa : oracle_comp spec A) (a : A) :
    ⟦oa⟧ a = 0 ↔ a ∉ oa.support :=
(pmf.apply_eq_zero_iff ⟦oa⟧ a).trans
  (iff_of_eq $ congr_arg not (congr_arg (has_mem.mem a) $ support_eval_distribution oa))

@[simp]
lemma eval_distribution_ne_zero_iff_mem_support (oa : oracle_comp spec A) (a : A) :
  ⟦oa⟧ a ≠ 0 ↔ a ∈ oa.support :=
by rw [ne.def, eval_distribution_eq_zero_iff_not_mem_support, set.not_not_mem]

@[simp]
lemma eval_distribution_eq_one_iff_support_subset_singleton (oa : oracle_comp spec A) (a : A) :
  ⟦oa⟧ a = 1 ↔ oa.support = {a} :=
by rw [pmf.apply_eq_one_iff, support_eval_distribution oa]

@[simp]
lemma eval_distribution_ge_zero_iff_mem_support (oa : oracle_comp spec A) (a : A) :
  0 < ⟦oa⟧ a ↔ a ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_distribution_ne_zero_iff_mem_support]

end support
