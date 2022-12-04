/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.pmf_stuff
import probability.probability_mass_function.uniform
import computational_monads.support.fin_support

/-!
# Distribution Semantics for Oracle Computations`

Big-step semantics for `oracle_comp`, associating a probability distribution to a computation.
For the purpose of this we assume that each oracle query has a uniform resulting distribution,
giving correct semantics for oracles like a `coin_oracle` or `uniform_selecting` oracle.

The resulting type is given by a `pmf`, the mathlib def of a probability mass function,
given by a regular function into `ℝ≥0∞` combined with a proof that it has sum `1`.
The mapping respects the monadic structures on `pmf` and `oracle_comp`,
  sending `return` to `pmf.pure` and `>>=` to `pmf.bind`.
-/

namespace distribution_semantics

open oracle_comp oracle_spec
open_locale classical big_operators ennreal

variables {α β γ : Type} {spec : oracle_spec} [finite_range spec]

/- Big step semantics for a computation with finite range oracles
The result of queries is assumed to be uniform over the oracle's codomain,
  independent of the given domain values in each query.
Usually the `spec` when calling this would just be `coin_oracle` or `uniform_selecting`,
However it can be any more general things as well, e.g. a dice rolling oracle -/
-- private noncomputable def eval_dist' {spec : oracle_spec} [h' : spec.finite_range] :
--   Π {α : Type} (oa : oracle_comp spec α), Σ (pa : pmf α), plift (pa.support = oa.support)
-- | _ (pure' α a) := ⟨pmf.pure a, plift.up $ (pmf.support_pure a)⟩
-- | _ (bind' α β oa ob) := ⟨(eval_dist' oa).1.bind (λ a, (eval_dist' $ ob a).1), begin
--         refine plift.up (set.ext $ λ b, _),
--         erw pmf.mem_support_bind_iff,
--         simp only [support, plift.down (eval_dist' oa).2, set.mem_Union],
--         split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩;
--           simpa [(plift.down (eval_dist' (ob a)).2)] using ha'
--       end⟩
-- | _ (query i t) := ⟨pmf.uniform_of_fintype (spec.range i),
--       plift.up ((pmf.support_uniform_of_fintype (spec.range i)))⟩

-- noncomputable def eval_dist (oa : oracle_comp spec α) : pmf α :=
-- (eval_dist' oa).1

noncomputable def eval_dist {spec : oracle_spec} [h : spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α), pmf α
| _ (pure' α a) := pmf.pure a
| _ (bind' α β oa ob) := pmf.bind (eval_dist oa) (λ a, eval_dist $ ob a)
| _ (query i t) := pmf.uniform_of_fintype (spec.range i)

notation `⦃` oa `⦄` := eval_dist oa

notation oa ` ≃ₚ ` oa' := ⦃oa⦄ = ⦃oa'⦄

variables (a : α) (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β)
  (oc oc' : α → β → oracle_comp spec γ) (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (f : α → β) (g : β → γ) (x x' : α) (y y' : β) (z z' : γ)

section support

@[simp] lemma support_eval_dist : ⦃oa⦄.support = oa.support :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { exact pmf.support_pure a },
  { refine (set.ext $ λ x, _),
    simp only [eval_dist, pmf.mem_support_bind_iff, hoa, hob, mem_support_bind'_iff] },
  { rw [eval_dist, pmf.support_uniform_of_fintype, support_query] }
end

@[simp] lemma eval_dist_eq_zero_iff_not_mem_support : ⦃oa⦄ x = 0 ↔ x ∉ oa.support :=
(pmf.apply_eq_zero_iff ⦃oa⦄ x).trans
  (iff_of_eq $ congr_arg not (congr_arg (has_mem.mem x) $ support_eval_dist oa))

@[simp] lemma eval_dist_ne_zero_iff_mem_support : ⦃oa⦄ x ≠ 0 ↔ x ∈ oa.support :=
by rw [ne.def, eval_dist_eq_zero_iff_not_mem_support, set.not_not_mem]

lemma eval_dist_eq_one_iff_support_eq_singleton : ⦃oa⦄ x = 1 ↔ oa.support = {x} :=
by rw [pmf.apply_eq_one_iff, support_eval_dist oa]

@[simp] lemma eval_dist_eq_one_iff_support_subset_singleton : ⦃oa⦄ x = 1 ↔ oa.support ⊆ {x} :=
(eval_dist_eq_one_iff_support_eq_singleton oa x).trans
  (set.nonempty.subset_singleton_iff $ support_nonempty oa).symm

@[simp] lemma eval_dist_pos_iff_mem_support : 0 < ⦃oa⦄ x ↔ x ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_dist_ne_zero_iff_mem_support]

variables {oa} {x}

lemma eval_dist_eq_zero_of_not_mem_support (h : x ∉ oa.support) : ⦃oa⦄ x = 0 :=
(eval_dist_eq_zero_iff_not_mem_support oa x).2 h

lemma eval_dist_ne_zero_of_not_mem_support (h : x ∈ oa.support) : ⦃oa⦄ x ≠ 0 :=
(eval_dist_ne_zero_iff_mem_support oa x).2 h

lemma eval_dist_eq_one_of_support_eq_singleton (h : oa.support = {x}) : ⦃oa⦄ x = 1 :=
(eval_dist_eq_one_iff_support_eq_singleton oa x).2 h

lemma eval_dist_eq_one_of_support_subset_singleton (h : oa.support ⊆ {x}) : ⦃oa⦄ x = 1 :=
(eval_dist_eq_one_iff_support_subset_singleton oa x).2 h

lemma eval_dist_pos_of_mem_support (h : x ∈ oa.support) : 0 < ⦃oa⦄ x :=
(eval_dist_pos_iff_mem_support oa x).2 h

end support

section fin_support

variables [computable spec] [decidable oa]

lemma support_eval_dist_eq_fin_support : ⦃oa⦄.support = oa.fin_support :=
(support_eval_dist oa).trans (coe_fin_support_eq_support oa).symm

lemma eval_dist_eq_zero_iff_not_mem_fin_support : ⦃oa⦄ x = 0 ↔ x ∉ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_eq_zero_iff_not_mem_support]

lemma eval_dist_ne_zero_iff_mem_fin_support : ⦃oa⦄ x ≠ 0 ↔ x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_ne_zero_iff_mem_support]

lemma eval_dist_eq_one_iff_fin_support_eq_singleton : ⦃oa⦄ x = 1 ↔ oa.fin_support = {x} :=
by simp only [fin_support_eq_iff_support_eq_coe, finset.coe_singleton,
  eval_dist_eq_one_iff_support_eq_singleton]

lemma eval_dist_eq_one_iff_fin_support_subset_singleton : ⦃oa⦄ x = 1 ↔ oa.fin_support ⊆ {x} :=
by simp only [fin_support_subset_iff_support_subset_coe, finset.coe_singleton,
  eval_dist_eq_one_iff_support_subset_singleton]

lemma eval_dist_pos_iff_mem_fin_support : 0 < ⦃oa⦄ x ↔ x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_pos_iff_mem_support]

variables {oa} {x}

lemma eval_dist_eq_zero_of_not_mem_fin_support (h : x ∉ oa.fin_support) : ⦃oa⦄ x = 0 :=
(eval_dist_eq_zero_iff_not_mem_fin_support oa x).2 h

lemma eval_dist_ne_zero_of_not_mem_fin_support (h : x ∈ oa.fin_support) : ⦃oa⦄ x ≠ 0 :=
(eval_dist_ne_zero_iff_mem_fin_support oa x).2 h

lemma eval_dist_eq_one_of_fin_support_eq_singleton (h : oa.fin_support = {x}) : ⦃oa⦄ x = 1 :=
(eval_dist_eq_one_iff_fin_support_eq_singleton oa x).2 h

lemma eval_dist_eq_one_of_fin_support_subset_singleton (h : oa.fin_support ⊆ {x}) : ⦃oa⦄ x = 1 :=
(eval_dist_eq_one_iff_fin_support_subset_singleton oa x).2 h

lemma eval_dist_pos_of_mem_fin_support (h : x ∈ oa.fin_support) : 0 < ⦃oa⦄ x :=
(eval_dist_pos_iff_mem_fin_support oa x).2 h

end fin_support

section return

@[simp] lemma eval_dist_return : ⦃(return a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_dist_return_apply : ⦃(return a : oracle_comp spec α)⦄ x = ite (x = a) 1 0 := rfl

lemma eval_dist_pure' : ⦃(pure' α a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_dist_pure'_apply : ⦃(pure' α a : oracle_comp spec α)⦄ x = ite (x = a) 1 0 := rfl

lemma eval_dist_pure : ⦃(pure a : oracle_comp spec α)⦄ = pmf.pure a := rfl

lemma eval_dist_pure_apply : ⦃(pure a : oracle_comp spec α)⦄ x = ite (x = a) 1 0 := rfl

@[simp] lemma eval_dist_return_apply_eq_one_iff :
  ⦃(return a : oracle_comp spec α)⦄ x = 1 ↔ x = a :=
by simp only [eval_dist_return_apply, ite_eq_iff, eq_self_iff_true,
  zero_ne_one, and_true, and_false, or_false]

@[simp] lemma eval_dist_return_apply_eq_zero_iff :
  ⦃(return a : oracle_comp spec α)⦄ x = 0 ↔ x ≠ a :=
by simp only [eval_dist_return_apply, ite_eq_iff, eq_self_iff_true,
  one_ne_zero, and_true, and_false, false_or]

lemma eval_dist_return_apply_self : ⦃(return a : oracle_comp spec α)⦄ a = 1 :=
by rw [eval_dist_return_apply_eq_one_iff]

lemma eval_dist_return_apply_of_ne {a x} (h : x ≠ a) :
  ⦃(return a : oracle_comp spec α)⦄ x = 0 :=
by simpa only [eval_dist_return, pmf.pure_apply, ite_eq_right_iff]

end return

section bind

@[simp] lemma eval_dist_bind : ⦃oa >>= ob⦄ = ⦃oa⦄.bind (λ x, ⦃ob x⦄) :=
by rw [← bind'_eq_bind, eval_dist]

lemma eval_dist_bind_apply_eq_tsum : ⦃oa >>= ob⦄ y = ∑' (x : α), ⦃oa⦄ x * ⦃ob x⦄ y :=
by simpa only [eval_dist_bind]

lemma eval_dist_bind_apply_eq_sum [spec.computable] [oa.decidable] :
  ⦃oa >>= ob⦄ y = ∑ x in oa.fin_support, ⦃oa⦄ x * ⦃ob x⦄ y :=
(eval_dist_bind_apply_eq_tsum oa ob y).trans (tsum_eq_sum $ λ a ha,
  by rw [(eval_dist_eq_zero_iff_not_mem_fin_support oa a).2 ha, zero_mul])

lemma eval_dist_bind' : ⦃bind' α β oa ob⦄ = ⦃oa⦄.bind (λ x, ⦃ob x⦄) := by rw eval_dist

lemma eval_dist_bind'_apply_eq_tsum : ⦃bind' α β oa ob⦄ y = ∑' (x : α), ⦃oa⦄ x * ⦃ob x⦄ y :=
by simpa only [eval_dist_bind']

lemma eval_dist_bind'_apply_eq_sum [spec.computable] [oa.decidable] :
  ⦃oa >>= ob⦄ y = ∑ x in oa.fin_support, ⦃oa⦄ x * ⦃ob x⦄ y :=
(eval_dist_bind'_apply_eq_tsum oa ob y).trans (tsum_eq_sum $ λ a ha,
  by rw [(eval_dist_eq_zero_iff_not_mem_fin_support oa a).2 ha, zero_mul])

lemma eval_dist_bind_bind_apply_eq_tsum_tsum : ⦃do {x ← oa, y ← ob x, oc x y}⦄ z
  = ∑' (x : α) (y : β), ⦃oa⦄ x * ⦃ob x⦄ y * ⦃oc x y⦄ z :=
by simp only [eval_dist_bind_apply_eq_tsum, ← ennreal.tsum_mul_left, mul_assoc]

lemma eval_dist_bind_bind_apply_eq_sum_sum [spec.computable] [oa.decidable]
  [∀ a, (ob a).decidable] : ⦃do {x ← oa, y ← ob x, oc x y}⦄ z =
    ∑ x in oa.fin_support, ∑ y in (ob x).fin_support, ⦃oa⦄ x * ⦃ob x⦄ y * ⦃oc x y⦄ z :=
by simp only [eval_dist_bind_apply_eq_sum, finset.mul_sum, mul_assoc]

lemma eval_dist_bind_eq_of_eval_dist_eq (hoa : ⦃oa⦄ = ⦃oa'⦄)
  (hob : ∀ a, ⦃ob a⦄ = ⦃ob' a⦄) : ⦃oa >>= ob⦄ = ⦃oa' >>= ob'⦄ :=
by simp_rw [eval_dist_bind, hoa, hob]

@[simp] lemma eval_dist_bind_return : ⦃oa >>= λ x, return (f x)⦄ = ⦃oa⦄.map f :=
by simp_rw [eval_dist_bind, eval_dist_return, pmf.bind_pure_comp]

lemma eval_dist_bind_return_apply :
  ⦃oa >>= λ x, return (f x)⦄ y = ∑' (x : α), ite (y = f x) (⦃oa⦄ x) 0 :=
by rw [eval_dist_bind_return, pmf.map_apply]

@[simp] lemma eval_dist_bind_return_id : ⦃oa >>= return⦄ = ⦃oa⦄ :=
(eval_dist_bind_return oa id).trans (by rw [pmf.map_id])

lemma eval_dist_return_bind : ⦃return a >>= ob⦄ = ⦃ob a⦄ :=
by simp only [eval_dist_bind, eval_dist_return, pmf.pure_bind]

lemma eval_dist_return_bind_apply : ⦃return a >>= ob⦄ y = ⦃ob a⦄ y :=
by simp only [eval_dist_bind, eval_dist_return, pmf.pure_bind]

end bind

section query

@[simp] lemma eval_dist_query : ⦃query i t⦄ = pmf.uniform_of_fintype (spec.range i) := rfl

lemma eval_dist_query_apply : ⦃query i t⦄ u = 1 / (fintype.card $ spec.range i) :=
by simp only [eval_dist_query, pmf.uniform_of_fintype_apply, one_div]

lemma eval_dist_query_bind_eq_tsum (oa : spec.range i → oracle_comp spec α) :
  ⦃query i t >>= oa⦄ x = (∑' u, ⦃oa u⦄ x) / (fintype.card $ spec.range i) :=
by simp_rw [eval_dist_bind_apply_eq_tsum, eval_dist_query_apply, div_eq_mul_inv,
  one_mul, ennreal.tsum_mul_left, mul_comm]

end query

section map

@[simp] lemma eval_dist_map : ⦃f <$> oa⦄ = ⦃oa⦄.map f := eval_dist_bind oa (pure ∘ f)

lemma eval_dist_map_apply [decidable_eq β] :
  ⦃f <$> oa⦄ y = ∑' (x : α), if y = f x then ⦃oa⦄ x else 0 :=
by simp only [eval_dist_map oa f, pmf.map_apply f ⦃oa⦄, @eq_comm β y]

lemma eval_dist_map_apply' [spec.computable] [decidable_eq β] [oa.decidable] :
  ⦃f <$> oa⦄ y = ∑ x in oa.fin_support, if y = f x then ⦃oa⦄ x else 0 :=
(eval_dist_map_apply oa f y).trans (tsum_eq_sum $ λ a ha,
  by simp only [eval_dist_eq_zero_of_not_mem_fin_support ha, if_t_t])

lemma eval_dist_map_return : ⦃f <$> (return x : oracle_comp spec α)⦄ = pmf.pure (f x) :=
by simp [eval_dist_map, pmf.map_pure]

lemma eval_dist_map_bind : ⦃g <$> (oa >>= ob)⦄ = ⦃oa⦄.bind (λ x, ⦃ob x⦄.map g) :=
by simp only [eval_dist_map, eval_dist_bind, pmf.map_bind]

end map

lemma eval_dist_bind_ite_apply_eq_tsum_add_tsum (p : α → Prop) [decidable_pred p]
  (f g : α → β) : ⦃oa >>= λ a, return (if p a then f a else g a)⦄ y =
  (∑' x, ite (p x ∧ y = f x) (⦃oa⦄ x) 0) + (∑' x, ite (¬ p x ∧ y = g x) (⦃oa⦄ x) 0) :=
begin
  rw [eval_dist_bind_return_apply, ← ennreal.tsum_add],
  refine tsum_congr (λ x, _),
  by_cases hpx : p x;
  simp only [hpx, if_true, true_and, not_true, false_and, if_false, add_zero,
    if_false, false_and, not_false_iff, true_and, zero_add]
end

/-- Right the `eval_dist` of bind as a sum over another type,
using a map that is both injective and surjective on corresponding supports -/
lemma helper {oa : oracle_comp spec α}
  {ob : α → oracle_comp spec β} {b : β} (g : γ → α)
  (h : ∀ x ∈ oa.support, b ∈ (ob x).support → x ∈ set.range g)
  (hg : ∀ x y, g x = g y → g x ∈ oa.support → b ∈ (ob (g x)).support → x = y) :
  ⦃oa >>= ob⦄ b = ∑' (c : γ), ⦃oa⦄ (g c) * ⦃ob (g c)⦄ b :=
begin
  rw [eval_dist_bind_apply_eq_tsum],
  refine tsum_eq_tsum_of_ne_zero_bij (g ∘ coe) _ _ (λ _, rfl),
  { intros x y h,
    have := x.2,
    simp only [subtype.val_eq_coe, function.support_mul, set.mem_inter_iff, function.mem_support,
      ne.def, eval_dist_eq_zero_iff_not_mem_support, set.not_not_mem] at this,
    refine hg ↑x ↑y h this.1 this.2 },
  { intros x hx,
    simp only [function.support_mul, set.mem_inter_iff, function.mem_support, ne.def,
      eval_dist_eq_zero_iff_not_mem_support, set.not_not_mem] at hx,
    specialize h x hx.1 hx.2,
    rw [set.mem_range] at h,
    obtain ⟨y, hy⟩ := h,
    rw [← hy, set.range_comp, set.mem_image],
    refine ⟨y, _, rfl⟩,
    rw [subtype.range_coe_subtype],
    simp only [hy, hx, function.support_mul, set.mem_inter_iff, function.mem_support,
      ne.def, eval_dist_eq_zero_iff_not_mem_support, set.not_not_mem, set.mem_set_of_eq, true_and] }
end

end distribution_semantics
