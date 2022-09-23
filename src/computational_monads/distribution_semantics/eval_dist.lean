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

variables {α β γ : Type} {spec spec' : oracle_spec}
variable [spec.finite_range]

/- Big step semantics for a computation with finite range oracles
  The result of queries is assumed to be uniform over the oracle's codomain,
    independent of the given domain values in each query.
  Usually the `spec` when calling this would just be `unit →ₒ bool` (i.e. a tape of random bits),
  However it can be any more general things as well, e.g. uniform sampling from finite sets
  
TODO: maybe `eval_dist` should be the public facing name (less letters :\ ) -/
private noncomputable def eval_dist' {spec : oracle_spec} [h' : spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α), Σ (pa : pmf α), plift (pa.support = oa.support)
| _ (pure' α a) := ⟨pmf.pure a, plift.up $ (pmf.support_pure a)⟩
| _ (bind' α β oa ob) := ⟨(eval_dist' oa).1.bind (λ a, (eval_dist' $ ob a).1), begin
        refine plift.up (set.ext $ λ b, _),
        erw pmf.mem_support_bind_iff,
        simp only [support, plift.down (eval_dist' oa).2, set.mem_Union],
        split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩;
          simpa [(plift.down (eval_dist' (ob a)).2)] using ha'
      end⟩
| _ (query i t) := ⟨pmf.uniform_of_fintype (spec.range i),
      plift.up ((pmf.support_uniform_of_fintype (spec.range i)))⟩

-- variables {α β γ : Type} {spec spec' : oracle_spec} (oa oa' : oracle_comp spec α)
--   (ob ob' : α → oracle_comp spec β) (oc oc' : α → β → oracle_comp spec γ)
--   (a a' : α) (b b' : β) (c c' : γ) (i : spec.ι) (t : spec.domain i)
-- variable [spec.finite_range]

noncomputable def eval_dist (oa : oracle_comp spec α) : pmf α :=
(eval_dist' oa).1

notation `⦃` oa `⦄` := eval_dist oa

section support

variables (oa : oracle_comp spec α) (a : α)

@[simp]
lemma support_eval_dist : ⦃oa⦄.support = oa.support := plift.down (eval_dist' oa).2

@[simp]
lemma eval_dist_eq_zero_iff_not_mem_support : ⦃oa⦄ a = 0 ↔ a ∉ oa.support :=
(pmf.apply_eq_zero_iff ⦃oa⦄ a).trans
  (iff_of_eq $ congr_arg not (congr_arg (has_mem.mem a) $ support_eval_dist oa))

@[simp]
lemma eval_dist_ne_zero_iff_mem_support : ⦃oa⦄ a ≠ 0 ↔ a ∈ oa.support :=
by rw [ne.def, eval_dist_eq_zero_iff_not_mem_support, set.not_not_mem]

@[simp]
lemma eval_dist_eq_one_iff_support_eq_singleton : ⦃oa⦄ a = 1 ↔ oa.support = {a} :=
by rw [pmf.apply_eq_one_iff, support_eval_dist oa]

@[simp]
lemma eval_dist_eq_one_iff_support_subset_singleton : ⦃oa⦄ a = 1 ↔ oa.support ⊆ {a} :=
(eval_dist_eq_one_iff_support_eq_singleton oa a).trans
  (set.nonempty.subset_singleton_iff $ support_nonempty oa).symm

@[simp]
lemma eval_dist_pos_iff_mem_support : 0 < ⦃oa⦄ a ↔ a ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_dist_ne_zero_iff_mem_support]

variables {oa} {a}

lemma eval_dist_eq_zero_of_not_mem_support (h : a ∉ oa.support) : ⦃oa⦄ a = 0 :=
(eval_dist_eq_zero_iff_not_mem_support oa a).2 h

lemma eval_dist_ne_zero_of_not_mem_support (h : a ∈ oa.support) : ⦃oa⦄ a ≠ 0 :=
(eval_dist_ne_zero_iff_mem_support oa a).2 h

lemma eval_dist_eq_one_of_support_eq_singleton (h : oa.support = {a}) : ⦃oa⦄ a = 1 :=
(eval_dist_eq_one_iff_support_eq_singleton oa a).2 h

lemma eval_dist_eq_one_of_support_subset_singleton (h : oa.support ⊆ {a}) : ⦃oa⦄ a = 1 :=
(eval_dist_eq_one_iff_support_subset_singleton oa a).2 h

lemma eval_dist_pos_of_mem_support (h : a ∈ oa.support) : 0 < ⦃oa⦄ a :=
(eval_dist_pos_iff_mem_support oa a).2 h

end support

section fin_support

variables [computable spec] (oa : oracle_comp spec α) [decidable oa] (a : α)

lemma support_eval_dist_eq_fin_support : ⦃oa⦄.support = oa.fin_support :=
(support_eval_dist oa).trans (coe_fin_support_eq_support oa).symm

lemma eval_dist_eq_zero_iff_not_mem_fin_support : ⦃oa⦄ a = 0 ↔ a ∉ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_eq_zero_iff_not_mem_support]

lemma eval_dist_ne_zero_iff_mem_fin_support : ⦃oa⦄ a ≠ 0 ↔ a ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_ne_zero_iff_mem_support]

lemma eval_dist_eq_one_iff_fin_support_eq_singleton : ⦃oa⦄ a = 1 ↔ oa.fin_support = {a} :=
by simp only [fin_support_eq_iff_support_eq_coe, finset.coe_singleton,
  eval_dist_eq_one_iff_support_eq_singleton]

lemma eval_dist_eq_one_iff_fin_support_subset_singleton : ⦃oa⦄ a = 1 ↔ oa.fin_support ⊆ {a} :=
by simp only [fin_support_subset_iff_support_subset_coe, finset.coe_singleton,
  eval_dist_eq_one_iff_support_subset_singleton]

lemma eval_dist_pos_iff_mem_fin_support : 0 < ⦃oa⦄ a ↔ a ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_pos_iff_mem_support]

variables {oa} {a}

lemma eval_dist_eq_zero_of_not_mem_fin_support (h : a ∉ oa.fin_support) : ⦃oa⦄ a = 0 :=
(eval_dist_eq_zero_iff_not_mem_fin_support oa a).2 h

lemma eval_dist_ne_zero_of_not_mem_fin_support (h : a ∈ oa.fin_support) : ⦃oa⦄ a ≠ 0 :=
(eval_dist_ne_zero_iff_mem_fin_support oa a).2 h

lemma eval_dist_eq_one_of_fin_support_eq_singleton (h : oa.fin_support = {a}) : ⦃oa⦄ a = 1 :=
(eval_dist_eq_one_iff_fin_support_eq_singleton oa a).2 h

lemma eval_dist_eq_one_of_fin_support_subset_singleton (h : oa.fin_support ⊆ {a}) : ⦃oa⦄ a = 1 :=
(eval_dist_eq_one_iff_fin_support_subset_singleton oa a).2 h

lemma eval_dist_pos_of_mem_fin_support (h : a ∈ oa.fin_support) : 0 < ⦃oa⦄ a :=
(eval_dist_pos_iff_mem_fin_support oa a).2 h

end fin_support

section return

variables (a a' : α)

@[simp]
lemma eval_dist_return : ⦃(return a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_dist_return_apply : ⦃(return a : oracle_comp spec α)⦄ a' =
  if a' = a then 1 else 0 := rfl

lemma eval_dist_pure' : ⦃(pure' α a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_dist_pure'_apply : ⦃(pure' α a : oracle_comp spec α)⦄ a' =
  if a' = a then 1 else 0 := rfl

lemma eval_dist_pure : ⦃(pure a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_dist_pure_apply : ⦃(pure a : oracle_comp spec α)⦄ a' =
  if a' = a then 1 else 0 := rfl

end return

section bind

variables (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : α → β → oracle_comp spec γ) (a a' : α) (b b' : β) (c c' : γ)

@[simp]
lemma eval_dist_bind : ⦃oa >>= ob⦄ = ⦃oa⦄.bind (λ a, ⦃ob a⦄) :=
by simp only [← bind'_eq_bind, eval_dist, eval_dist']

lemma eval_dist_bind_apply : ⦃oa >>= ob⦄ b = ∑' (a : α), ⦃oa⦄ a * ⦃ob a⦄ b :=
by simpa only [eval_dist_bind]

lemma eval_dist_bind_apply' [spec.computable] [oa.decidable] :
  ⦃oa >>= ob⦄ b = ∑ a in oa.fin_support, ⦃oa⦄ a * ⦃ob a⦄ b :=
(eval_dist_bind_apply oa ob b).trans (tsum_eq_sum $ λ a ha,
  by rw [(eval_dist_eq_zero_iff_not_mem_fin_support oa a).2 ha, zero_mul])

lemma eval_dist_bind' : ⦃bind' α β oa ob⦄ = ⦃oa⦄.bind (λ a, ⦃ob a⦄) :=
eval_dist_bind oa ob

lemma eval_dist_bind'_apply : ⦃bind' α β oa ob⦄ b = ∑' (a : α), ⦃oa⦄ a * ⦃ob a⦄ b :=
eval_dist_bind_apply oa ob b

lemma eval_dist_bind'_apply' [spec.computable] [oa.decidable] :
  ⦃bind' α β oa ob⦄ b = ∑ a in oa.fin_support, ⦃oa⦄ a * ⦃ob a⦄ b :=
eval_dist_bind_apply' oa ob b

@[simp]
lemma eval_dist_bind_bind_apply :
  ⦃do {a ← oa, b ← ob a, oc a b}⦄ c = ∑' (a : α) (b : β), ⦃oa⦄ a * (⦃ob a⦄ b * ⦃oc a b⦄ c) :=
(eval_dist_bind_apply oa _ c).trans
  (tsum_congr $ λ a, by simp only [eval_dist_bind_apply, nnreal.tsum_mul_left (⦃oa⦄ a)])

lemma eval_dist_bind_bind_apply' [spec.computable] [oa.decidable] [∀ a, (ob a).decidable] :
  ⦃do {a ← oa, b ← ob a, oc a b}⦄ c =
    ∑ a in oa.fin_support, ∑ b in (ob a).fin_support, ⦃oa⦄ a * (⦃ob a⦄ b * ⦃oc a b⦄ c) :=
(eval_dist_bind_apply' oa _ c).trans
  (finset.sum_congr rfl $ λ a ha, by simp only [eval_dist_bind_apply', finset.mul_sum])

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)

@[simp]
lemma eval_dist_query : ⦃query i t⦄ = pmf.uniform_of_fintype (spec.range i) := rfl

lemma eval_dist_query_apply : ⦃query i t⦄ u = 1 / (fintype.card $ spec.range i) :=
by simp only [eval_dist_query, pmf.uniform_of_fintype_apply, one_div]

end query

section map

variables (oa : oracle_comp spec α) (f : α → β)

@[simp]
lemma eval_dist_map (f : α → β) : ⦃f <$> oa⦄ = ⦃oa⦄.map f := eval_dist_bind oa (pure ∘ f)

lemma eval_dist_map_apply [decidable_eq β] (oa : oracle_comp spec α) (f : α → β) (b : β) :
  ⦃f <$> oa⦄ b = ∑' (a : α), if b = f a then ⦃oa⦄ a else 0 :=
by simp only [eval_dist_map oa f, pmf.map_apply f ⦃oa⦄, @eq_comm β b]

lemma eval_dist_map_apply' [spec.computable] [decidable_eq β] [oa.decidable]
  (f : α → β) (b : β) : ⦃f <$> oa⦄ b = ∑ a in oa.fin_support, if b = f a then ⦃oa⦄ a else 0 :=
(eval_dist_map_apply oa f b).trans (tsum_eq_sum $ λ a ha,
  by simp only [eval_dist_eq_zero_of_not_mem_fin_support ha, if_t_t])

end map

end distribution_semantics
