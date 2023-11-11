/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.pmf_stuff
import computational_monads.distribution_semantics.defs.fin_support

/-!
# Distribution Semantics for Oracle Computations

Denotational semantics for `oracle_comp`, associating a probability distribution to a computation.
For the purpose of this we assume that each oracle query has a uniform resulting distribution,
giving correct semantics for oracles like a `coin_oracle` or `uniform_selecting` oracle.
More general oracles need to first be simulated using `oracle_comp.simulate`,
in order to give the oracle's semantics in terms of simpler oracles like a coin oracle.

The resulting type is given by a `pmf`, the mathlib definition of a probability mass function,
given by a regular function into `ℝ≥0∞` combined with a proof that it has sum `1`.
The mapping respects monadic structures, sending `return` to `pmf.pure` and `>>=` to `pmf.bind`.

Note that the mapping is neither injective nor surjective onto `pmf`.
For example the computations `oa >>= λ _, return 5` and `return 5` both map to `pmf.pure 5`,
and no computation will map to .
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators

/- Denotational semantics for a computation with access to a set of oracles.
We assume that query results are uniformly distributed regardless of oracle inputs.
Usually the `spec` when calling this would just be `coin_oracle` or `uniform_selecting`,
as oracles like these are expected to return values essentially randomly.
For more complex oracles such as a random oracle which may not always respond randomly,
simulation semantics (`oracle_comp.simulate`) can be used to reduce the oracles of the computation.
This will give a new computation which only calls some uniform oracle,  -/
noncomputable def eval_dist {spec : oracle_spec} : Π {α : Type} (oa : oracle_comp spec α), pmf α
| _ (pure' α a) := pmf.pure a
| _ (query_bind' i t α oa) := pmf.bind
  (pmf.uniform_of_fintype (spec.range i)) (λ a, eval_dist $ oa a)

notation `⁅` oa `⁆` := eval_dist oa

-- notation `⁅=` x `|` oa `⁆` := ⁅oa⁆ x

variables {α β : Type} {spec : oracle_spec} (a : α) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (ou : spec.range i → oracle_comp spec α) (x : α) (y : β)

lemma eval_dist.ext (p : pmf α) (h : ∀ x, ⁅oa⁆ x = p x) : ⁅oa⁆ = p := pmf.ext h

lemma eval_dist.ext_iff (p : pmf α) : ⁅oa⁆ = p ↔ ∀ x, ⁅oa⁆ x = p x := pmf.ext_iff

@[simp] lemma eval_dist_return : ⁅(return a : oracle_comp spec α)⁆ = pmf.pure a := rfl

lemma eval_dist_pure' : ⁅(pure' α a : oracle_comp spec α)⁆ = pmf.pure a := rfl

lemma eval_dist_pure : ⁅(pure a : oracle_comp spec α)⁆ = pmf.pure a := rfl

lemma eval_dist_query_bind : ⁅query_bind' i t α ou⁆ = pmf.bind
  (pmf.uniform_of_fintype (spec.range i)) (λ a, eval_dist $ ou a) := by rw [eval_dist]


-- @[simp] lemma eval_dist_bind : ⁅oa >>= ob⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆) :=
-- by rw [← oracle_comp.bind'_eq_bind, eval_dist]

-- lemma eval_dist_bind' : ⁅bind' α β oa ob⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆) := eval_dist_bind oa ob

-- @[simp] lemma eval_dist_query : ⁅query i t⁆ = pmf.uniform_of_fintype (spec.range i) := rfl

section support

/-- The support of the `pmf` associated to a computation is the coercion of its `support`. -/
@[simp] lemma support_eval_dist : ⁅oa⁆.support = oa.support :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa,
  { rw [oracle_comp.pure'_eq_return],
    exact pmf.support_pure a },


  -- induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  -- { exact pmf.support_pure a },
  -- { exact (set.ext $ λ x, by simp_rw [support_bind, set.mem_Union, ← oracle_comp.bind'_eq_bind,
  --     eval_dist, pmf.mem_support_bind_iff, hoa, hob]) },
  -- { rw [eval_dist, pmf.support_uniform_of_fintype, support_query, set.top_eq_univ] }
end

/-- The support of the `pmf` associated to a computation is the coercion of its `fin_support`. -/
lemma support_eval_dist_eq_fin_support : ⁅oa⁆.support = ↑oa.fin_support :=
(support_eval_dist oa).trans (coe_fin_support_eq_support oa).symm

@[simp] lemma eval_dist_apply_eq_zero_iff : ⁅oa⁆ x = 0 ↔ x ∉ oa.support :=
by rw [pmf.apply_eq_zero_iff, support_eval_dist]

lemma eval_dist_apply_eq_zero_iff' : ⁅oa⁆ x = 0 ↔ x ∉ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, eval_dist_apply_eq_zero_iff]

@[simp] lemma eval_dist_apply_ne_zero_iff : ⁅oa⁆ x ≠ 0 ↔ x ∈ oa.support :=
by rw [ne.def, eval_dist_apply_eq_zero_iff, set.not_not_mem]

lemma eval_dist_apply_ne_zero_iff' : ⁅oa⁆ x ≠ 0 ↔ x ∈ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, eval_dist_apply_ne_zero_iff]

lemma eval_dist_apply_eq_one_iff : ⁅oa⁆ x = 1 ↔ oa.support = {x} :=
by rw [pmf.apply_eq_one_iff, support_eval_dist oa]

lemma eval_dist_apply_eq_one_iff' : ⁅oa⁆ x = 1 ↔ oa.fin_support = {x} :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_singleton, eval_dist_apply_eq_one_iff]

@[simp] lemma eval_dist_apply_eq_one_iff_subset : ⁅oa⁆ x = 1 ↔ oa.support ⊆ {x} :=
(eval_dist_apply_eq_one_iff oa x).trans
  (set.nonempty.subset_singleton_iff $ support_nonempty oa).symm

lemma eval_dist_apply_eq_one_iff_subset' : ⁅oa⁆ x = 1 ↔ oa.fin_support ⊆ {x} :=
by rw [fin_support_subset_iff_support_subset_coe, finset.coe_singleton,
  eval_dist_apply_eq_one_iff_subset]

@[simp] lemma eval_dist_apply_pos_iff : 0 < ⁅oa⁆ x ↔ x ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_dist_apply_ne_zero_iff]

lemma eval_dist_apply_pos_iff' : 0 < ⁅oa⁆ x ↔ x ∈ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, eval_dist_apply_pos_iff]

variables {oa} {x}

lemma eval_dist_apply_eq_zero (h : x ∉ oa.support) : ⁅oa⁆ x = 0 :=
(eval_dist_apply_eq_zero_iff oa x).2 h

lemma eval_dist_apply_eq_zero' (h : x ∉ oa.fin_support) : ⁅oa⁆ x = 0 :=
(eval_dist_apply_eq_zero_iff' oa x).2 h

lemma eval_dist_apply_ne_zero (h : x ∈ oa.support) : ⁅oa⁆ x ≠ 0 :=
(eval_dist_apply_ne_zero_iff oa x).2 h

lemma eval_dist_apply_ne_zero' (h : x ∈ oa.fin_support) : ⁅oa⁆ x ≠ 0 :=
(eval_dist_apply_ne_zero_iff' oa x).2 h

lemma eval_dist_apply_eq_one (h : oa.support = {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_apply_eq_one_iff oa x).2 h

lemma eval_dist_apply_eq_one' (h : oa.fin_support = {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_apply_eq_one_iff' oa x).2 h

lemma eval_dist_apply_eq_one_of_subset (h : oa.support ⊆ {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_apply_eq_one_iff_subset oa x).2 h

lemma eval_dist_apply_eq_one_of_subset' (h : oa.fin_support ⊆ {x}) : ⁅oa⁆ x = 1 :=
(eval_dist_apply_eq_one_iff_subset' oa x).2 h

lemma eval_dist_apply_pos (h : x ∈ oa.support) : 0 < ⁅oa⁆ x :=
(eval_dist_apply_pos_iff oa x).2 h

lemma eval_dist_apply_pos' (h : x ∈ oa.fin_support) : 0 < ⁅oa⁆ x :=
(eval_dist_apply_pos_iff' oa x).2 h

end support

end oracle_comp
