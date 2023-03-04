/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.pmf_stuff
import probability.probability_mass_function.uniform
import computational_monads.support.monad

/-!
# Distribution Semantics for Oracle Computations

Big-step semantics for `oracle_comp`, associating a probability distribution to a computation.
For the purpose of this we assume that each oracle query has a uniform resulting distribution,
giving correct semantics for oracles like a `coin_oracle` or `uniform_selecting` oracle.
More general oracles need to first be simulated using `oracle_comp.simulate`,
in order to give the oracle's semantics in terms of simpler oracles like a coin oracle.

The resulting type is given by a `pmf`, the mathlib definition of a probability mass function,
given by a regular function into `ℝ≥0∞` combined with a proof that it has sum `1`.
The mapping respects monadic structures, sending `return` to `pmf.pure` and `>>=` to `pmf.bind`.

Note that the mapping is neither injective nor surjective onto `pmf`.
For example the computations `oa >>= λ _, return 5` and `return 5` both map to `pmf.pure 5`,
and the resulting distribution will always have rational values for probability masses.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

/- Big step semantics for a computation with access to a set of oracles.
We assume that query results are uniformly distributed regardless of oracle inputs.
Usually the `spec` when calling this would just be `coin_oracle` or `uniform_selecting`,
as oracles like these are expected to return values essentially randomly.
For more complex oracles such as a random oracle which may not always respond randomly,
simulation semantics (`oracle_comp.simulate`) can be used to reduce the oracles of the computation.
This will give a new computation which only calls some uniform oracle,  -/
noncomputable def eval_dist {spec : oracle_spec} :
  Π {α : Type} (oa : oracle_comp spec α), pmf α
| _ (pure' α a) := pmf.pure a
| _ (bind' α β oa ob) := pmf.bind (eval_dist oa) (λ a, eval_dist $ ob a)
| _ (query i t) := pmf.uniform_of_fintype (spec.range i)

notation `⁅` oa `⁆` := eval_dist oa

notation `⁅=` x `|` oa `⁆` := ⁅oa⁆ x

lemma eval_dist.ext (oa : oracle_comp spec α) (p : pmf α)
  (h : ∀ x, ⁅= x | oa⁆ = p x) : ⁅oa⁆ = p := pmf.ext h

lemma eval_dist.ext_iff (oa : oracle_comp spec α) (p : pmf α) :
  ⁅oa⁆ = p ↔ ∀ x, ⁅= x | oa⁆ = p x := pmf.ext_iff _ _

section support

variables (oa : oracle_comp spec α) (x : α)

@[simp] lemma support_eval_dist : ⁅oa⁆.support = oa.support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact pmf.support_pure a },
  { refine (set.ext $ λ x, by simp_rw [mem_support_bind_iff, ← bind'_eq_bind, eval_dist,
      pmf.mem_support_bind_iff, hoa, hob]) },
  { rw [eval_dist, pmf.support_uniform_of_fintype, support_query] }
end

@[simp] lemma eval_dist_eq_zero_iff_not_mem_support : ⁅oa⁆ x = 0 ↔ x ∉ oa.support :=
by rw [pmf.apply_eq_zero_iff, support_eval_dist]

@[simp] lemma eval_dist_ne_zero_iff_mem_support : ⁅oa⁆ x ≠ 0 ↔ x ∈ oa.support :=
by rw [ne.def, eval_dist_eq_zero_iff_not_mem_support, set.not_not_mem]

lemma eval_dist_eq_one_iff_support_eq_singleton : ⁅oa⁆ x = 1 ↔ oa.support = {x} :=
by rw [pmf.apply_eq_one_iff, support_eval_dist oa]

@[simp] lemma eval_dist_eq_one_iff_support_subset_singleton : ⁅oa⁆ x = 1 ↔ oa.support ⊆ {x} :=
(eval_dist_eq_one_iff_support_eq_singleton oa x).trans
  (set.nonempty.subset_singleton_iff $ support_nonempty oa).symm

@[simp] lemma eval_dist_pos_iff_mem_support : 0 < ⁅oa⁆ x ↔ x ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_dist_ne_zero_iff_mem_support]

variables {oa} {x}

-- TODO: cumbersome naming `--> eval_dist_eq_zero`, `eval_dist_ne_zero`, ...
lemma eval_dist_eq_zero_of_not_mem_support (h : x ∉ oa.support) : ⁅oa⁆ x = 0 :=
(eval_dist_eq_zero_iff_not_mem_support oa x).2 h

lemma eval_dist_ne_zero_of_not_mem_support (h : x ∈ oa.support) : ⁅oa⁆ x ≠ 0 :=
(eval_dist_ne_zero_iff_mem_support oa x).2 h

lemma eval_dist_eq_one_of_support_eq_singleton (h : oa.support = {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_eq_one_iff_support_eq_singleton oa x).2 h

lemma eval_dist_eq_one_of_support_subset_singleton (h : oa.support ⊆ {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_eq_one_iff_support_subset_singleton oa x).2 h

lemma eval_dist_pos_of_mem_support (h : x ∈ oa.support) : 0 < ⁅oa⁆ x :=
(eval_dist_pos_iff_mem_support oa x).2 h

end support

-- TODO: merging these sections would probably be good very being maintainable.
section fin_support

variables (oa : oracle_comp spec α) [decidable oa] (x : α)

lemma support_eval_dist_eq_fin_support : ⁅oa⁆.support = oa.fin_support :=
(support_eval_dist oa).trans (coe_fin_support_eq_support oa).symm

lemma eval_dist_eq_zero_iff_not_mem_fin_support : ⁅oa⁆ x = 0 ↔ x ∉ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_eq_zero_iff_not_mem_support]

lemma eval_dist_ne_zero_iff_mem_fin_support : ⁅oa⁆ x ≠ 0 ↔ x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_ne_zero_iff_mem_support]

lemma eval_dist_eq_one_iff_fin_support_eq_singleton : ⁅oa⁆ x = 1 ↔ oa.fin_support = {x} :=
by simp only [fin_support_eq_iff_support_eq_coe, finset.coe_singleton,
  eval_dist_eq_one_iff_support_eq_singleton]

lemma eval_dist_eq_one_iff_fin_support_subset_singleton : ⁅oa⁆ x = 1 ↔ oa.fin_support ⊆ {x} :=
by simp only [fin_support_subset_iff_support_subset_coe, finset.coe_singleton,
  eval_dist_eq_one_iff_support_subset_singleton]

lemma eval_dist_pos_iff_mem_fin_support : 0 < ⁅oa⁆ x ↔ x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, eval_dist_pos_iff_mem_support]

variables {oa} {x}

lemma eval_dist_eq_zero_of_not_mem_fin_support (h : x ∉ oa.fin_support) : ⁅oa⁆ x = 0 :=
(eval_dist_eq_zero_iff_not_mem_fin_support oa x).2 h

lemma eval_dist_ne_zero_of_not_mem_fin_support (h : x ∈ oa.fin_support) : ⁅oa⁆ x ≠ 0 :=
(eval_dist_ne_zero_iff_mem_fin_support oa x).2 h

lemma eval_dist_eq_one_of_fin_support_eq_singleton (h : oa.fin_support = {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_eq_one_iff_fin_support_eq_singleton oa x).2 h

lemma eval_dist_eq_one_of_fin_support_subset_singleton (h : oa.fin_support ⊆ {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_eq_one_iff_fin_support_subset_singleton oa x).2 h

lemma eval_dist_pos_of_mem_fin_support (h : x ∈ oa.fin_support) : 0 < ⁅oa⁆ x :=
(eval_dist_pos_iff_mem_fin_support oa x).2 h

end fin_support

section return

variables (a x : α)

@[simp] lemma eval_dist_return : ⁅(return a : oracle_comp spec α)⁆ = pmf.pure a := rfl

/-- In general the probability of getting `x` from `return a` is based on `set.indicator`. -/
@[simp] lemma eval_dist_return_apply_eq_indicator :
  ⁅(return a : oracle_comp spec α)⁆ x = set.indicator {a} (λ _, 1) x := rfl

/-- Given a decidable equality instance, the probability of `x` from `return a` can be given by
a simple if-then statement rather than by `set.indicator`. -/
@[simp] lemma eval_dist_return_apply [decidable_eq α] :
  ⁅(return a : oracle_comp spec α)⁆ x = ite (x = a) 1 0 := by convert rfl

lemma eval_dist_pure' : ⁅(pure' α a : oracle_comp spec α)⁆ = pmf.pure a := rfl

lemma eval_dist_pure'_apply_eq_indicator :
  ⁅(pure' α a : oracle_comp spec α)⁆ x = set.indicator {a} (λ _, 1) x := rfl

lemma eval_dist_pure'_apply [decidable_eq α] :
  ⁅(pure' α a : oracle_comp spec α)⁆ x = ite (x = a) 1 0 := by convert rfl

lemma eval_dist_pure : ⁅(pure a : oracle_comp spec α)⁆ = pmf.pure a := rfl

lemma eval_dist_pure_apply_eq_indicator :
  ⁅(pure a : oracle_comp spec α)⁆ x = set.indicator {a} (λ _, 1) x := rfl

lemma eval_dist_pure_apply [decidable_eq α] :
  ⁅(pure a : oracle_comp spec α)⁆ x = ite (x = a) 1 0 := by convert rfl

end return

section bind

variables (a : α) (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) (f : α → β)
  (x : α) (y : β)

@[simp] lemma eval_dist_bind : ⁅oa >>= ob⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆) :=
by rw [← bind'_eq_bind, eval_dist]

lemma eval_dist_bind' : ⁅bind' α β oa ob⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆) := eval_dist_bind oa ob

lemma eval_dist_bind_apply_eq_tsum : ⁅oa >>= ob⁆ y = ∑' x, ⁅oa⁆ x * ⁅ob x⁆ y :=
by simpa only [eval_dist_bind]

lemma eval_dist_bind_apply_eq_sum [fintype α] : ⁅oa >>= ob⁆ y = ∑ x, ⁅oa⁆ x * ⁅ob x⁆ y :=
by simpa only [eval_dist_bind_apply_eq_tsum]
  using tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim)

lemma eval_dist_bind_apply_eq_sum_fin_support [oa.decidable] :
  ⁅oa >>= ob⁆ y = ∑ x in oa.fin_support, ⁅oa⁆ x * ⁅ob x⁆ y :=
(eval_dist_bind_apply_eq_tsum oa ob y).trans (tsum_eq_sum $ λ a ha,
  by rw [(eval_dist_eq_zero_iff_not_mem_fin_support oa a).2 ha, zero_mul])

end bind

section query

variables (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (oa : spec.range i → oracle_comp spec α) (x : α)

@[simp] lemma eval_dist_query : ⁅query i t⁆ = pmf.uniform_of_fintype (spec.range i) := rfl

lemma eval_dist_query_apply : ⁅query i t⁆ u = 1 / (fintype.card $ spec.range i) :=
by simp only [eval_dist_query, pmf.uniform_of_fintype_apply, one_div]

end query

end oracle_comp
