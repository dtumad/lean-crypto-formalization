import to_mathlib.general
import probability.probability_mass_function.uniform
import computational_monads.support.fin_support

/-!
# Distribution Semantics for Oracle Computations`

Big-step semantics for `oracle_comp`, associating a probability distribution to a computation.
The resulting type is given by a `pmf`, the mathlib def of a probability mass function.

-/

namespace distribution_semantics

open oracle_comp oracle_spec
open_locale classical big_operators nnreal ennreal

/- Big step semantics for a computation with finite range oracles
  The result of queries is assumed to be uniform over the oracle's codomain,
    independent of the given domain values in each query.
  Usually the `spec` when calling this would just be `unit →ₒ bool` (i.e. a tape of random bits),
  However it can be any more general things as well, e.g. uniform sampling from finite sets
  
TODO: maybe `eval_dist` should be the public facing name (less letters :\ ) -/
private noncomputable def eval_dist {spec : oracle_spec} [h' : spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α), Σ (pa : pmf α), plift (pa.support = oa.support)
| _ (pure' α a) := ⟨pmf.pure a, plift.up $ (pmf.support_pure a)⟩
| _ (bind' α β oa ob) := ⟨(eval_dist oa).1.bind (λ a, (eval_dist $ ob a).1), begin
        refine plift.up (set.ext $ λ b, _),
        erw pmf.mem_support_bind_iff,
        simp only [support, plift.down (eval_dist oa).2, set.mem_Union],
        split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩;
          simpa [(plift.down (eval_dist (ob a)).2)] using ha'
      end⟩
| _ (query i t) := ⟨pmf.uniform_of_fintype (spec.range i),
      plift.up ((pmf.support_uniform_of_fintype (spec.range i)))⟩

variables {α β γ : Type} {spec spec' : oracle_spec}
  (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (a a' : α) (b b' : β) (i : spec.ι) (t : spec.domain i)
variable [spec.finite_range]

noncomputable def eval_distribution (oa : oracle_comp spec α) : pmf α :=
(eval_dist oa).1

notation `⦃` oa `⦄` := eval_distribution oa

section return

@[simp]
lemma eval_distribution_return : ⦃(return a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_distribution_return_apply : ⦃(return a : oracle_comp spec α)⦄ a' =
  if a' = a then 1 else 0 := rfl

lemma eval_distribution_pure' : ⦃(pure' α a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_distribution_pure'_apply : ⦃(pure' α a : oracle_comp spec α)⦄ a' =
  if a' = a then 1 else 0 := rfl

lemma eval_distribution_pure : ⦃(pure a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_distribution_pure_apply : ⦃(pure a : oracle_comp spec α)⦄ a' =
  if a' = a then 1 else 0 := rfl

end return

section bind

@[simp]
lemma eval_distribution_bind : ⦃oa >>= ob⦄ = ⦃oa⦄.bind (λ a, ⦃ob a⦄) :=
by simp only [← bind'_eq_bind, eval_distribution, eval_dist]

lemma eval_distribution_bind_apply : ⦃oa >>= ob⦄ b = ∑' (a : α), ⦃oa⦄ a * ⦃ob a⦄ b :=
by simpa only [eval_distribution_bind]

lemma eval_distribution_bind' : ⦃bind' α β oa ob⦄ = ⦃oa⦄.bind (λ a, ⦃ob a⦄) :=
eval_distribution_bind oa ob

lemma eval_distribution_bind'_apply : ⦃oa >>= ob⦄ b = ∑' (a : α), ⦃oa⦄ a * ⦃ob a⦄ b :=
eval_distribution_bind_apply oa ob b

@[simp]
lemma eval_distribution_bind_bind_apply (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) (c : γ) :
  ⦃do {a ← oa, b ← ob a, oc a b}⦄ c = ∑' (a : α) (b : β), ⦃oa⦄ a * (⦃ob a⦄ b * ⦃oc a b⦄ c) :=
(eval_distribution_bind_apply oa _ c).trans
  (tsum_congr $ λ a, by simp only [eval_distribution_bind_apply, nnreal.tsum_mul_left (⦃oa⦄ a)])

end bind

section query

@[simp]
lemma eval_distribution_query (i : spec.ι) (t : spec.domain i) :
  ⦃query i t⦄ = pmf.uniform_of_fintype (spec.range i) :=
rfl

lemma eval_distribution_query_apply (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  ⦃query i t⦄ u = 1 / (fintype.card $ spec.range i) :=
by simp only [eval_distribution_query, pmf.uniform_of_fintype_apply, one_div]

end query

section map

@[simp]
lemma eval_distribution_map (oa : oracle_comp spec α) (f : α → β) :
  ⦃f <$> oa⦄ = ⦃oa⦄.map f :=
eval_distribution_bind oa (pure ∘ f)

lemma eval_distribution_map_apply [decidable_eq β] (oa : oracle_comp spec α) (f : α → β) (b : β) :
  ⦃f <$> oa⦄ b = ∑' (a : α), if b = f a then ⦃oa⦄ a else 0 :=
by simp only [eval_distribution_map oa f, pmf.map_apply f ⦃oa⦄, @eq_comm β b]

end map

section support

@[simp]
lemma support_eval_distribution (oa : oracle_comp spec α) : ⦃oa⦄.support = oa.support :=
plift.down (eval_dist oa).2

lemma support_eval_distribution_eq_fin_support [spec.computable] (oa : oracle_comp spec α)
  [decidable oa] : ⦃oa⦄.support = oa.fin_support :=
(support_eval_distribution oa).trans (coe_fin_support_eq_support oa).symm

@[simp]
lemma eval_distribution_eq_zero_iff_not_mem_support (oa : oracle_comp spec α) (a : α) :
    ⦃oa⦄ a = 0 ↔ a ∉ oa.support :=
(pmf.apply_eq_zero_iff ⦃oa⦄ a).trans
  (iff_of_eq $ congr_arg not (congr_arg (has_mem.mem a) $ support_eval_distribution oa))

lemma eval_distribution_eq_zero_of_not_mem_support {oa : oracle_comp spec α} {a : α}
  (h : a ∉ oa.support) : ⦃oa⦄ a = 0 :=
(eval_distribution_eq_zero_iff_not_mem_support oa a).2 h

@[simp]
lemma eval_distribution_ne_zero_iff_mem_support (oa : oracle_comp spec α) (a : α) :
  ⦃oa⦄ a ≠ 0 ↔ a ∈ oa.support :=
by rw [ne.def, eval_distribution_eq_zero_iff_not_mem_support, set.not_not_mem]

lemma eval_distribution_ne_zero_of_not_mem_support {oa : oracle_comp spec α} (a : α)
  (h : a ∈ oa.support) : ⦃oa⦄ a ≠ 0 :=
(eval_distribution_ne_zero_iff_mem_support oa a).2 h

@[simp]
lemma eval_distribution_eq_one_iff_support_eq_singleton (oa : oracle_comp spec α) (a : α) :
  ⦃oa⦄ a = 1 ↔ oa.support = {a} :=
by rw [pmf.apply_eq_one_iff, support_eval_distribution oa]

lemma eval_distribution_eq_one_of_support_eq_singleton {oa : oracle_comp spec α} {a : α}
  (h : oa.support = {a}) : ⦃oa⦄ a = 1 :=
(eval_distribution_eq_one_iff_support_eq_singleton oa a).2 h

@[simp]
lemma eval_distribution_eq_one_iff_support_subset_singleton (oa : oracle_comp spec α) (a : α) :
  ⦃oa⦄ a = 1 ↔ oa.support ⊆ {a} :=
(eval_distribution_eq_one_iff_support_eq_singleton oa a).trans
  (set.nonempty.subset_singleton_iff $ support_nonempty oa).symm

lemma eval_distribution_eq_one_of_support_subset_singleton {oa : oracle_comp spec α} (a : α)
  (h : oa.support ⊆ {a}) : ⦃oa⦄ a = 1 :=
(eval_distribution_eq_one_iff_support_subset_singleton oa a).2 h

@[simp]
lemma eval_distribution_pos_iff_mem_support (oa : oracle_comp spec α) (a : α) :
  0 < ⦃oa⦄ a ↔ a ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_distribution_ne_zero_iff_mem_support]

lemma eval_distribution_pos_of_mem_support {oa : oracle_comp spec α} {a : α}
  (h : a ∈ oa.support) : 0 < ⦃oa⦄ a :=
(eval_distribution_pos_iff_mem_support oa a).2 h

end support

section fin_support


end fin_support

end distribution_semantics
