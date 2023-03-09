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

/- Big step semantics for a computation with access to a set of oracles.
We assume that query results are uniformly distributed regardless of oracle inputs.
Usually the `spec` when calling this would just be `coin_oracle` or `uniform_selecting`,
as oracles like these are expected to return values essentially randomly.
For more complex oracles such as a random oracle which may not always respond randomly,
simulation semantics (`oracle_comp.simulate`) can be used to reduce the oracles of the computation.
This will give a new computation which only calls some uniform oracle,  -/
noncomputable def eval_dist {spec : oracle_spec} : Π {α : Type} (oa : oracle_comp spec α), pmf α
| _ (pure' α a) := pmf.pure a
| _ (bind' α β oa ob) := pmf.bind (eval_dist oa) (λ a, eval_dist $ ob a)
| _ (query i t) := pmf.uniform_of_fintype (spec.range i)

notation `⁅` oa `⁆` := eval_dist oa

notation `⁅=` x `|` oa `⁆` := ⁅oa⁆ x

variables {α β : Type} {spec : oracle_spec} (a : α) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (i : spec.ι) (t : spec.domain i) (u : spec.range i) (x : α) (y : β)

lemma eval_dist.ext (oa : oracle_comp spec α) (p : pmf α)
  (h : ∀ x, ⁅= x | oa⁆ = p x) : ⁅oa⁆ = p := pmf.ext h

lemma eval_dist.ext_iff (oa : oracle_comp spec α) (p : pmf α) :
  ⁅oa⁆ = p ↔ ∀ x, ⁅= x | oa⁆ = p x := pmf.ext_iff _ _

@[simp] lemma eval_dist_return : ⁅(return a : oracle_comp spec α)⁆ = pmf.pure a := rfl

/-- The probability of getting `x` from `return a` is `1` if `x = a` and `0` if `x ≠ a`.
In general this probability is defined in terms of `set.indicator` applied to a singleton set,
since a definition in terms of if-then-else requires decidable equality of the type `α`.  -/
@[simp] lemma eval_dist_return_apply_eq_indicator :
  ⁅= x | (return a : oracle_comp spec α)⁆ = set.indicator {a} (λ _, 1) x := rfl

/-- Given a decidable equality instance, the probability of `x` from `return a` can be given by
a simple if-then statement rather than by `set.indicator`. -/
@[simp] lemma eval_dist_return_apply [decidable_eq α] :
  ⁅= x | (return a : oracle_comp spec α)⁆ = ite (x = a) 1 0 := by convert rfl

lemma eval_dist_pure' : ⁅(pure' α a : oracle_comp spec α)⁆ = pmf.pure a := rfl

lemma eval_dist_pure'_apply_eq_indicator :
  ⁅= x | (pure' α a : oracle_comp spec α)⁆ = set.indicator {a} (λ _, 1) x := rfl

lemma eval_dist_pure'_apply [decidable_eq α] :
  ⁅= x | (pure' α a : oracle_comp spec α)⁆ = ite (x = a) 1 0 := by convert rfl

lemma eval_dist_pure : ⁅(pure a : oracle_comp spec α)⁆ = pmf.pure a := rfl

lemma eval_dist_pure_apply_eq_indicator :
  ⁅= x | (pure a : oracle_comp spec α)⁆ = set.indicator {a} (λ _, 1) x := rfl

lemma eval_dist_pure_apply [decidable_eq α] :
  ⁅= x | (pure a : oracle_comp spec α)⁆ = ite (x = a) 1 0 := by convert rfl

@[simp] lemma eval_dist_bind : ⁅oa >>= ob⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆) :=
by rw [← bind'_eq_bind, eval_dist]

/-- The probability of `oa >>= ob` returning `y` is the sum over all `x` of the probability
of getting `y` from `ob x`, weighted by the probability of getting `x` from `oa`. -/
lemma eval_dist_bind_apply_eq_tsum : ⁅= y | oa >>= ob⁆ = ∑' x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
by rw [eval_dist_bind, pmf.bind_apply]

/-- Express the probability of getting `y` from `oa >>= ob` as a finite sum,
assuming that the underlying return type `α` of `oa` is itself finite. -/
lemma eval_dist_bind_apply_eq_sum [fintype α] :
  ⁅= y | oa >>= ob⁆ = ∑ x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
by simpa only [eval_dist_bind_apply_eq_tsum]
  using tsum_eq_sum (λ x hx, (hx $ finset.mem_univ x).elim)

lemma eval_dist_bind' : ⁅bind' α β oa ob⁆ = ⁅oa⁆.bind (λ x, ⁅ob x⁆) := eval_dist_bind oa ob

lemma eval_dist_bind'_apply_eq_tsum : ⁅= y | bind' α β oa ob⁆ = ∑' x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ :=
eval_dist_bind_apply_eq_tsum oa ob y

lemma eval_dist_bind'_apply_eq_sum [fintype α] :
  ⁅= y | bind' α β oa ob⁆ = ∑ x, ⁅= x | oa⁆ * ⁅= y | ob x⁆ := eval_dist_bind_apply_eq_sum oa ob y

@[simp] lemma eval_dist_query : ⁅query i t⁆ = pmf.uniform_of_fintype (spec.range i) := rfl

/-- The chance of getting a result `u` from `query i t` is uniform over the output type. -/
lemma eval_dist_query_apply : ⁅= u | query i t⁆ = 1 / (fintype.card $ spec.range i) :=
by rw [eval_dist_query, pmf.uniform_of_fintype_apply, one_div]

lemma eval_dist_query_apply_eq_inv : ⁅= u | query i t⁆ = (fintype.card $ spec.range i)⁻¹ :=
by rw [eval_dist_query, pmf.uniform_of_fintype_apply]

section support

@[simp] lemma support_eval_dist : ⁅oa⁆.support = oa.support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { exact pmf.support_pure a },
  { exact (set.ext $ λ x, by simp_rw [mem_support_bind_iff, ← bind'_eq_bind, eval_dist,
      pmf.mem_support_bind_iff, hoa, hob]) },
  { rw [eval_dist, pmf.support_uniform_of_fintype, support_query] }
end

@[simp] lemma eval_dist_eq_zero_iff : ⁅= x | oa⁆ = 0 ↔ x ∉ oa.support :=
by rw [pmf.apply_eq_zero_iff, support_eval_dist]

@[simp] lemma eval_dist_ne_zero_iff : ⁅= x | oa⁆ ≠ 0 ↔ x ∈ oa.support :=
by rw [ne.def, eval_dist_eq_zero_iff, set.not_not_mem]

lemma eval_dist_eq_one_iff : ⁅= x | oa⁆ = 1 ↔ oa.support = {x} :=
by rw [pmf.apply_eq_one_iff, support_eval_dist oa]

@[simp] lemma eval_dist_eq_one_iff' : ⁅= x | oa⁆ = 1 ↔ oa.support ⊆ {x} :=
(eval_dist_eq_one_iff oa x).trans (set.nonempty.subset_singleton_iff $ support_nonempty oa).symm

@[simp] lemma eval_dist_pos_iff : 0 < ⁅= x | oa⁆ ↔ x ∈ oa.support :=
by rw [pos_iff_ne_zero, eval_dist_ne_zero_iff]

variables {oa} {x}

-- TODO: cumbersome naming `--> eval_dist_eq_zero`, `eval_dist_ne_zero`, ...
lemma eval_dist_eq_zero (h : x ∉ oa.support) : ⁅= x | oa⁆ = 0 := (eval_dist_eq_zero_iff oa x).2 h

lemma eval_dist_ne_zero (h : x ∈ oa.support) : ⁅= x | oa⁆ ≠ 0 := (eval_dist_ne_zero_iff oa x).2 h

lemma eval_dist_eq_one (h : oa.support = {x}) : ⁅= x | oa⁆ = 1 := (eval_dist_eq_one_iff oa x).2 h

lemma eval_dist_eq_one' (h : oa.support ⊆ {x}) : ⁅= x | oa⁆ = 1 := (eval_dist_eq_one_iff' oa x).2 h

lemma eval_dist_pos (h : x ∈ oa.support) : 0 < ⁅= x | oa⁆ := (eval_dist_pos_iff oa x).2 h

end support

-- TODO: merging these sections would probably be good very being maintainable.
section fin_support

variables [decidable oa]

lemma support_eval_dist_eq_fin_support : ⁅oa⁆.support = oa.fin_support :=
(support_eval_dist oa).trans (coe_fin_support_eq_support oa).symm

lemma eval_dist_eq_zero_iff_not_mem_fin_support : ⁅= x | oa⁆ = 0 ↔ x ∉ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, eval_dist_eq_zero_iff]

lemma eval_dist_ne_zero_iff_mem_fin_support : ⁅= x | oa⁆ ≠ 0 ↔ x ∈ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, eval_dist_ne_zero_iff]

lemma eval_dist_eq_one_iff_fin_support_eq_singleton : ⁅= x | oa⁆ = 1 ↔ oa.fin_support = {x} :=
by rw [fin_support_eq_iff_support_eq_coe, finset.coe_singleton,
  eval_dist_eq_one_iff]

lemma eval_dist_eq_one_iff_fin_support_subset_singleton : ⁅= x | oa⁆ = 1 ↔ oa.fin_support ⊆ {x} :=
by rw [fin_support_subset_iff_support_subset_coe, finset.coe_singleton,
  eval_dist_eq_one_iff']

lemma eval_dist_pos_iff_mem_fin_support : 0 < ⁅= x | oa⁆ ↔ x ∈ oa.fin_support :=
by rw [mem_fin_support_iff_mem_support, eval_dist_pos_iff]

variables {oa} {x}

lemma eval_dist_eq_zero_of_not_mem_fin_support (h : x ∉ oa.fin_support) : ⁅= x | oa⁆ = 0 :=
(eval_dist_eq_zero_iff_not_mem_fin_support oa x).2 h

lemma eval_dist_ne_zero_of_not_mem_fin_support (h : x ∈ oa.fin_support) : ⁅= x | oa⁆ ≠ 0 :=
(eval_dist_ne_zero_iff_mem_fin_support oa x).2 h

lemma eval_dist_eq_one_of_fin_support_eq_singleton (h : oa.fin_support = {x}) : ⁅= x | oa⁆ = 1 :=
(eval_dist_eq_one_iff_fin_support_eq_singleton oa x).2 h

lemma eval_dist_eq_one_of_fin_support_subset_singleton (h : oa.fin_support ⊆ {x}) :
  ⁅= x | oa⁆ = 1 :=
(eval_dist_eq_one_iff_fin_support_subset_singleton oa x).2 h

lemma eval_dist_pos_of_mem_fin_support (h : x ∈ oa.fin_support) : 0 < ⁅= x | oa⁆ :=
(eval_dist_pos_iff_mem_fin_support oa x).2 h

end fin_support

end oracle_comp
