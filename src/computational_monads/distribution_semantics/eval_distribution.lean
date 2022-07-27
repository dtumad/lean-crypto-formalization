import to_mathlib.general
import computational_monads.support

/-!
# Distribution Semantics for Oracle Computations`

Big-step semantics for `oracle_comp`, associating a probability distribution to a computation.
The resulting type is given by a `pmf`, the mathlib def of a probability mass function.

-/

namespace distribution_semantics

open oracle_comp oracle_spec
open_locale big_operators nnreal ennreal

/- Big step semantics for a computation with finite range oracles
  The result of queries is assumed to be uniform over the oracle's codomain,
    independent of the given domain values in each query.
  Usually the `spec` when calling this would just be `unit →ₒ bool` (i.e. a tape of random bits),
  However it can be any more general things as well, e.g. uniform sampling from finite sets -/
private noncomputable def eval_dist {spec : oracle_spec} [h' : spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α), Σ (pa : pmf α), plift (pa.support = oa.support)
| _ (pure' α a) := ⟨pmf.pure a, plift.up $ (pmf.support_pure a)⟩
| _ (bind' α β oa ob) := ⟨(eval_dist oa).1 >>= λ a, (eval_dist $ ob a).1, begin
        refine plift.up (set.ext $ λ b, _),
        erw pmf.mem_support_bind_iff,
        simp only [support, plift.down (eval_dist oa).2, set.mem_Union],
        split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩;
          simpa [(plift.down (eval_dist (ob a)).2)] using ha'
      end⟩
| _ (query i t) := ⟨pmf.uniform_of_fintype (spec.range i),
      plift.up ((pmf.support_uniform_of_fintype (spec.range i)))⟩

variables {α β γ : Type} {spec : oracle_spec}
variable [spec.finite_range]

noncomputable def eval_distribution (oa : oracle_comp spec α) : pmf α :=
(eval_dist oa).1

notation `⦃` oa `⦄` := eval_distribution oa

@[simp]
lemma eval_distribution_pure (a : α) :
  ⦃(pure a : oracle_comp spec α)⦄ = pmf.pure a :=
rfl

@[simp]
lemma eval_distribution_pure_apply [decidable_eq α] (a a' : α) :
  ⦃(pure a : oracle_comp spec α)⦄ a' = if a' = a then 1 else 0 :=
by convert (pmf.pure_apply a a')

@[simp]
lemma eval_distribution_return (a : α) :
  ⦃(return a : oracle_comp spec α)⦄ = pmf.pure a :=
rfl

@[simp]
lemma eval_distribution_return_apply [decidable_eq α] (a a' : α) :
  ⦃(return a : oracle_comp spec α)⦄ a' = if a' = a then 1 else 0 :=
eval_distribution_pure_apply a a'

@[simp]
lemma eval_distribution_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  ⦃oa >>= ob⦄ = ⦃oa⦄ >>= λ a, ⦃ob a⦄ := 
by simp [eval_distribution, eval_dist, -bind'_eq_bind, bind]

@[simp]
lemma eval_distribution_bind_apply (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (b : β) :
  ⦃oa >>= ob⦄ b = ∑' (a : α), ⦃oa⦄ a * ⦃ob a⦄ b :=
by simpa only [eval_distribution_bind]

@[simp]
lemma eval_distribution_bind_bind_apply (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) (c : γ) :
  ⦃do {a ← oa, b ← ob a, oc a b}⦄ c = ∑' (a : α) (b : β), ⦃oa⦄ a * (⦃ob a⦄ b * ⦃oc a b⦄ c) :=
(eval_distribution_bind_apply oa _ c).trans
  (tsum_congr $ λ a, by simp only [eval_distribution_bind_apply, nnreal.tsum_mul_left (⦃oa⦄ a)])

@[simp]
lemma eval_distribution_map (oa : oracle_comp spec α) (f : α → β) :
  ⦃f <$> oa⦄ = ⦃oa⦄.map f :=
eval_distribution_bind oa (pure ∘ f)

@[simp]
lemma eval_distribution_map_apply [decidable_eq β] (oa : oracle_comp spec α) (f : α → β) (b : β) :
  ⦃f <$> oa⦄ b = ∑' (a : α), if f a = b then ⦃oa⦄ a else 0 :=
by simp only [eval_distribution_map oa f, pmf.map_apply f ⦃oa⦄, @eq_comm β b]

@[simp]
lemma eval_distribution_query (i : spec.ι) (t : spec.domain i) :
  ⦃query i t⦄ = pmf.uniform_of_fintype (spec.range i) :=
rfl

@[simp]
lemma eval_distribution_query_apply (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  ⦃query i t⦄ u = 1 / (fintype.card $ spec.range i) :=
by simp only [eval_distribution_query, pmf.uniform_of_fintype_apply, one_div]

section support

@[simp]
lemma support_eval_distribution (oa : oracle_comp spec α) :
  ⦃oa⦄.support = oa.support :=
plift.down (eval_dist oa).2

@[simp]
lemma eval_distribution_eq_zero_iff_not_mem_support (oa : oracle_comp spec α) (a : α) :
    ⦃oa⦄ a = 0 ↔ a ∉ oa.support :=
(pmf.apply_eq_zero_iff ⦃oa⦄ a).trans
  (iff_of_eq $ congr_arg not (congr_arg (has_mem.mem a) $ support_eval_distribution oa))

@[simp]
lemma eval_distribution_ne_zero_iff_mem_support (oa : oracle_comp spec α) (a : α) :
  ⦃oa⦄ a ≠ 0 ↔ a ∈ oa.support :=
by rw [ne.def, eval_distribution_eq_zero_iff_not_mem_support, set.not_not_mem]

@[simp]
lemma eval_distribution_eq_one_iff_support_subset_singleton (oa : oracle_comp spec α) (a : α) :
  ⦃oa⦄ a = 1 ↔ oa.support = {a} :=
by rw [pmf.apply_eq_one_iff, support_eval_distribution oa]

@[simp]
lemma eval_distribution_ge_zero_iff_mem_support (oa : oracle_comp spec α) (a : α) :
  0 < ⦃oa⦄ a ↔ a ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_distribution_ne_zero_iff_mem_support]

end support

end distribution_semantics
