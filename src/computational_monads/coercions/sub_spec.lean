/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.stateless_oracle
import computational_monads.constructions.uniform_select

/-!
# Coercions Between Computations With Additional Oracles

This file defines a `is_sub_spec` relation for pairs of `oracle_spec` where one can be
thought of as an extension of the other with additional oracles.
The definition consists of a function from query inputs in the original oracle to a
computation using the new set of oracles, such that the result of the mapping
doesn't affect the underlying probability distribution on the oracle call.

We use the notation `spec ⊂ₒ spec'` to represent that one set of oracles is a subset of another,
where the non-exclusive subset symbol reflects that we avoid defining this instance reflexively.
This decision is based on the `is_coe` construction, where we don't want to coerce a computation
to itself by calling a reflexive `is_sub_spec` construction.

We define the map to output a computation rather than a new set of oracle inputs in the new spec
to avoid type checking issues, as the `query` output type will not be definitionally equal
to the `query` output type in the original `oracle_spec`, causing issues in defining `has_coe`.
In practice the mapping will still usually output a `query` call,
and the equality between the underlying distributions is generally sufficient.

From this definition we construct a `is_coe` instance to coerce a computation with one set of
oracles to one with a larger set of oracles, using the `is_sub_spec` to call `simulate'`.
We show that this coercion has no effect on `support`, `eval_dist`, or `prob_event`.
-/

namespace oracle_spec

open oracle_comp distribution_semantics

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation. -/
class is_sub_spec (spec spec' : oracle_spec) :=
(to_fun (i : spec.ι) : spec.domain i → oracle_comp spec' (spec.range i))
(eval_dist_to_fun' : ∀ i t, ⁅to_fun i t⁆ = ⁅query i t⁆)

infixl ` ⊂ₒ `:65 := is_sub_spec

namespace is_sub_spec

variables (spec spec' : oracle_spec) [h : spec ⊂ₒ spec']

@[simp] lemma support_to_fun  (i : spec.ι) (t : spec.domain i) : (h.to_fun i t).support = ⊤ :=
by rw [← support_eval_dist, h.eval_dist_to_fun', support_eval_dist, support_query]

@[simp] lemma fin_support_to_fun [∀ i t, (h.to_fun i t).decidable]
  (i : spec.ι) (t : spec.domain i) : (h.to_fun i t).fin_support = ⊤ :=
by simp only [fin_support_eq_iff_support_eq_coe, finset.top_eq_univ,
  support_to_fun, set.top_eq_univ, finset.coe_univ]

@[simp] lemma eval_dist_to_fun (i : spec.ι) (t : spec.domain i) :
  ⁅h.to_fun i t⁆ = pmf.uniform_of_fintype (spec.range i) :=
by rw [h.eval_dist_to_fun', eval_dist_query] 

@[simp] lemma prob_event_to_fun (i : spec.ι) (t : spec.domain i) (e : set (spec.range i)) :
  ⁅e | h.to_fun i t⁆ = ⁅e | query i t⁆ :=
prob_event_eq_of_eval_dist_eq (h.eval_dist_to_fun' i t) e

end is_sub_spec

end oracle_spec

namespace oracle_comp

open oracle_spec distribution_semantics

instance coe_sub_spec (spec spec' : oracle_spec) [h : spec ⊂ₒ spec'] (α : Type) :
  has_coe (oracle_comp spec α) (oracle_comp spec' α) :=
{coe := default_simulate' ⟪λ i t, h.to_fun i t⟫}

variables (spec spec' : oracle_spec) [spec ⊂ₒ spec'] {α β : Type}

instance coe_sub_spec.decidable [∀ i t, (@is_sub_spec.to_fun spec spec' _ i t).decidable]
  (oa : oracle_comp spec α) [oa.decidable] : (↑oa : oracle_comp spec' α).decidable :=
simulate'.decidable _ oa ()

@[simp] lemma support_coe_sub_spec (oa : oracle_comp spec α) :
  (↑oa : oracle_comp spec' α).support = oa.support :=
stateless_oracle.support_simulate'_eq_support _ _ ()
  (λ i t, is_sub_spec.support_to_fun spec spec' i t)  

@[simp] lemma fin_support_coe_sub_spec [∀ i t, (@is_sub_spec.to_fun spec spec' _ i t).decidable]
  (oa : oracle_comp spec α) [oa.decidable] :
  (↑oa : oracle_comp spec' α).fin_support = oa.fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_coe_sub_spec]

@[simp] lemma eval_dist_coe_sub_spec (oa : oracle_comp spec α) :
  ⁅(↑oa : oracle_comp spec' α)⁆ = ⁅oa⁆ :=
stateless_oracle.eval_dist_simulate'_eq_eval_dist _ _ ()
  (λ i t, is_sub_spec.eval_dist_to_fun spec spec' i t)  

@[simp] lemma prob_event_coe_sub_spec (oa : oracle_comp spec α) (e : set α) :
  ⁅e | (↑oa : oracle_comp spec' α)⁆ = ⁅e | oa⁆ :=
stateless_oracle.prob_event_simulate'_eq_prob_event _ _ ()
  (λ i t, is_sub_spec.eval_dist_to_fun spec spec' i t) e  

end oracle_comp

namespace oracle_spec

open oracle_comp distribution_semantics

/-- coerce a coin flip into a uniform random selection of a `bool` -/
@[priority std.priority.default+100]
instance : is_sub_spec coin_spec uniform_selecting :=
{ to_fun := λ i t, $ᵛ (tt ::ᵥ ff ::ᵥ vector.nil),
  eval_dist_to_fun' := λ i t, pmf.ext (λ x, by cases x;
    simp_rw [eval_dist_uniform_select_vector_apply, vector.to_list_cons,
      vector.to_list_nil, list.count_cons, list.count_nil, eq_self_iff_true, if_true, if_false,
      eval_dist_query_apply, card_range_coin_spec, nat.cast_one]) }

/-- Coerce a computation to one with access to another oracle on the left,
forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default]
instance is_sub_spec_append_left (spec spec' : oracle_spec) : spec ⊂ₒ (spec' ++ spec) :=
{ to_fun := λ i t, @query (spec' ++ spec) (sum.inr i) t,
  eval_dist_to_fun' := λ i t, trans (eval_dist_query (sum.inr i) t) (eval_dist_query i t).symm }

/-- Coerce a computation to one with access to another oracle on the right,
forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default+1]
instance is_sub_spec_append_right (spec spec' : oracle_spec) : spec ⊂ₒ (spec ++ spec') :=
{ to_fun := λ i t, @query (spec ++ spec') (sum.inl i) t,
  eval_dist_to_fun' := λ i t, trans (eval_dist_query (sum.inl i) t) (eval_dist_query i t).symm }

/-- Coerce an oracle and then append to the left. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default+10]
instance is_sub_spec_append_left_of_is_sub_spec (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec sub_spec (spec ++ super_spec) :=
{ to_fun := λ i t, ↑(h.to_fun i t),
  eval_dist_to_fun' := λ i t,by rw [eval_dist_coe_sub_spec, is_sub_spec.eval_dist_to_fun'] }


/-- Coerce an oracle and then append to the right. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default+11]
instance is_sub_spec_append_right_of_is_sub_spec (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec sub_spec (super_spec ++ spec) :=
{ to_fun := λ i t, ↑(h.to_fun i t),
  eval_dist_to_fun' := λ i t,by rw [eval_dist_coe_sub_spec, is_sub_spec.eval_dist_to_fun'] }

/-- Coerce the oracle on the right side of an existing set of appended oracles. -/
@[priority std.priority.default+20]
instance is_sub_spec_left_side_append (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec (sub_spec ++ spec) (super_spec ++ spec) :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, (append.range_inl sub_spec spec i).symm.rec (h.to_fun i t)
  | (sum.inr i) := λ t, @query (super_spec ++ _) (sum.inr i) t
  end,
  eval_dist_to_fun' := λ i, match i with
  | (sum.inl i) := λ t, (eval_dist_coe_sub_spec _ _ (h.to_fun i t)).trans
    ((h.eval_dist_to_fun' i t).trans rfl)
  | (sum.inr i) := λ t, rfl
  end }

/-- Coerce the oracle on the right side of an existing set of appended oracles. -/
@[priority std.priority.default+21]
instance is_sub_spec_right_side_append (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec (spec ++ sub_spec) (spec ++ super_spec) :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, @query (_ ++ super_spec) (sum.inl i) t
  | (sum.inr i) := λ t, (append.range_inr spec sub_spec i).symm.rec (h.to_fun i t)
  end,
  eval_dist_to_fun' := λ i, match i with
  | (sum.inl i) := λ t, rfl
  | (sum.inr i) := λ t, (eval_dist_coe_sub_spec _ _ (h.to_fun i t)).trans
      ((h.eval_dist_to_fun' i t).trans rfl)
  end }

/-- Coerce towards a standardized append ordering (matching the `infixl` declaration for `++`) -/
@[priority std.priority.default+30]
instance is_sub_spec_assoc (spec spec' spec'' : oracle_spec) :
  is_sub_spec (spec ++ (spec' ++ spec'')) (spec ++ spec' ++ spec'') :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, @query (spec ++ spec' ++ spec'') (sum.inl (sum.inl i)) t
  | (sum.inr (sum.inl i)) := λ t, @query (spec ++ spec' ++ spec'') (sum.inl (sum.inr i)) t
  | (sum.inr (sum.inr i)) := λ t, @query (spec ++ spec' ++ spec'') (sum.inr i) t
  end,
  eval_dist_to_fun' := λ i, match i with
  | (sum.inl i) := λ t, rfl
  | (sum.inr (sum.inl i)) := λ t, rfl
  | (sum.inr (sum.inr i)) := λ t, rfl
  end }

end oracle_spec

namespace oracle_spec

open oracle_comp

section examples

-- This set of examples serves as sort of a "unit test" for the coercions above
variables (spec spec' spec'' spec''' : oracle_spec) (coe_spec coe_spec' : oracle_spec)
  [coe_spec ⊂ₒ coe_spec'] {α β : Type}

-- coerce a single `coin_spec` and then append extra oracles
example (oa : oracle_comp coe_spec α) :
  oracle_comp (coe_spec' ++ spec' ++ spec'') α := ↑oa
example (oa : oracle_comp coe_spec α) :
  oracle_comp (spec ++ coe_spec' ++ spec') α := ↑oa
example (oa : oracle_comp coe_spec α) :
  oracle_comp (spec ++ spec' ++ coe_spec') α := ↑oa

-- coerce left side of append and then append on additional oracles
example (oa : oracle_comp (coe_spec ++ spec) α) :
  oracle_comp (coe_spec' ++ spec ++ spec') α := ↑oa
example (oa : oracle_comp (coe_spec ++ spec) α) :
  oracle_comp (coe_spec' ++ spec' ++ spec) α := ↑oa
example (oa : oracle_comp (coe_spec ++ spec) α) :
  oracle_comp (spec' ++ coe_spec' ++ spec) α := ↑oa

-- coerce right side of append and then append on additional oracles
example (oa : oracle_comp (spec ++ coe_spec) α) :
  oracle_comp (spec ++ coe_spec' ++ spec') α := ↑oa
example (oa : oracle_comp (spec ++ coe_spec) α) :
  oracle_comp (spec ++ spec' ++ coe_spec') α := ↑oa
example (oa : oracle_comp (spec ++ coe_spec) α) :
  oracle_comp (spec' ++ spec ++ coe_spec') α := ↑oa

-- coerce an inside part while also applying associativity
example (oa : oracle_comp (spec ++ (spec' ++ coe_spec)) α) :
  oracle_comp (spec ++ spec' ++ coe_spec') α := ↑oa
example (oa : oracle_comp (spec ++ (coe_spec ++ spec')) α) :
  oracle_comp (spec ++ coe_spec' ++ spec') α := ↑oa
example (oa : oracle_comp (coe_spec ++ (spec ++ spec')) α) :
  oracle_comp (coe_spec' ++ spec ++ spec') α := ↑oa

-- coerce two oracles up to four oracles
example (oa : oracle_comp (spec ++ spec') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec'') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec' ++ spec'') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec'' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa

-- coerce threee oracles up to four oracles
example (oa : oracle_comp (spec ++ spec' ++ spec'') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec'' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec' ++ spec'' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa

-- four oracles with associativity and internal coercion
example (oa : oracle_comp ((coe_spec ++ spec') ++ (spec'' ++ spec''')) α) :
  oracle_comp (coe_spec' ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp ((spec ++ spec') ++ (coe_spec ++ spec''')) α) :
  oracle_comp (spec ++ spec' ++ coe_spec' ++ spec''') α := ↑oa
example (oa : oracle_comp ((spec ++ coe_spec) ++ (spec'' ++ spec''')) α) :
  oracle_comp (spec ++ coe_spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp ((spec ++ spec') ++ (spec'' ++ coe_spec')) α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ coe_spec') α := ↑oa

/-- coercion makes it possible to mix computations on individual oracles -/
example {spec : oracle_spec} : oracle_comp (uniform_selecting ++ spec) bool := 
do { n ←$[0..10], b ← coin, if n ≤ 3 ∧ b = tt then return ff else coin }

end examples

end oracle_spec
