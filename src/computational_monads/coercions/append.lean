/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.identity_oracle
import computational_monads.simulation_semantics.simulate.subsingleton
import computational_monads.coercions.coin

/-!
# Coercions Between Computations With Additional Oracles

This file provides a number of `has_coe` instances for different `oracle_comp` computations.
This is a very powerful tool when defining computations in terms of simpler versions.

The main coercions are for the append operation on `oracle_spec`,
  allowing an increase the number of oracles in a number of ways.
This allows a computation to be written by composing computations using fewer oracles.

The coercions are ordered very specifically using priority attributes,
  to ensure that they can converge to anything in a sort of 'standard form'
In particular, can coerce to any set of appended oracles assuming that:
1. The target oracle list is fully left associated, which is the same associativity as `++`.
2. The subset of original oracles in the target is in the same order.

To match this we adopt both conventions in general, and use a standard ordering for all oracles.
In particular we start with the basic finite oracles: `coin_spec ++ uniform_selecting ++ ...`,
  and then add additional oracles further in the list. This standard ordering allows most coercions
  between oracles to happen automatically.
-/

namespace oracle_comp

open oracle_spec distribution_semantics 

variables (spec spec' spec'' spec''' : oracle_spec)
  (coe_spec coe_spec' coe_spec'' coe_spec''' : oracle_spec)
  (S S' : Type) {α : Type}
 
section coe_append_right

/-- Coerce a computation to one with access to another oracle on the right,
  forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default-50]
instance coe_append_right (α) : has_coe (oracle_comp spec α) (oracle_comp (spec ++ spec') α) :=
{ coe := default_simulate' ⟪λ i, let i' : (spec ++ spec').ι := sum.inl i in query i'⟫ }

variable (oa : oracle_comp spec α)

lemma coe_append_right.def : (↑oa : oracle_comp (spec ++ spec') α) =
  oa.default_simulate' ⟪λ i t, let i' : (spec ++ spec').ι := sum.inl i in query i' t⟫ := rfl

instance coe_append_right.decidable [oa.decidable] :
  (↑oa : oracle_comp (spec ++ spec') α).decidable :=
begin
  refine @simulate'.decidable _ _ _ _ _ oa () _ _ (λ i t s, _),
  rw [stateless_oracle.apply_eq],
  apply_instance,
end

/-- Coercing to an extra oracle on the right doesn't affect a computation's `support`. -/
@[simp] lemma support_coe_append_right :
  (↑oa : oracle_comp (spec ++ spec') α).support = oa.support :=
stateless_oracle.support_simulate'_eq_support _ _ () (λ _ _, support_query _ _)

/-- Coercing to an extra oracle on the right doesn't affect a computation's `fin_support`. -/
@[simp] lemma fin_support_coe_append_right [oa.decidable] :
  (↑oa : oracle_comp (spec ++ spec') α).fin_support = oa.fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_coe_append_right]

/-- Coercing to an extra oracle on the right doesn't affect a computation's `eval_dist`. -/
@[simp] lemma eval_dist_coe_append_right :
  ⁅(↑oa : oracle_comp (spec ++ spec') α)⁆ = ⁅oa⁆ :=
stateless_oracle.eval_dist_simulate'_eq_eval_dist _ _ _ (λ i t, rfl)

/-- Coercing to an extra oracle on the right doesn't affect a computation's `prob_event`. -/
@[simp] lemma prob_event_coe_append_right (e : set α) :
  ⁅e | (↑oa : oracle_comp (spec ++ spec') α)⁆ = ⁅e | oa⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_coe_append_right _ _ oa) e

end coe_append_right

section coe_append_left

/-- Coerce a computation to one with access to another oracle on the left,
  forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default-51]
instance coe_append_left (α) : has_coe (oracle_comp spec α) (oracle_comp (spec' ++ spec) α) :=
{ coe := default_simulate' ⟪λ i, let i' : (spec' ++ spec).ι := sum.inr i in query i'⟫ }

variable (oa : oracle_comp spec α)

lemma coe_append_left.def : (↑oa : oracle_comp (spec' ++ spec) α) =
  oa.default_simulate' ⟪λ i t, let i' : (spec' ++ spec).ι := sum.inr i in query i' t⟫ := rfl

instance coe_append_left.decidable [oa.decidable] :
  (↑oa : oracle_comp (spec' ++ spec) α).decidable :=
begin
  refine @simulate'.decidable _ _ _ _ _ oa () _ _ (λ i t s, _),
  rw [stateless_oracle.apply_eq],
  apply_instance,
end

/-- Coercing to an extra oracle on the left doesn't affect a computation's `support`. -/
@[simp] lemma support_coe_append_left :
  (↑oa : oracle_comp (spec' ++ spec) α).support = oa.support :=
stateless_oracle.support_simulate'_eq_support _ _ () (λ _ _, support_query _ _)

/-- Coercing to an extra oracle on the left doesn't affect a computation's `fin_support`. -/
@[simp] lemma fin_support_coe_append_left [oa.decidable] :
  (↑oa : oracle_comp (spec' ++ spec) α).fin_support = oa.fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_coe_append_left]

/-- Coercing to an extra oracle on the left doesn't affect a computation's `eval_dist`. -/
@[simp] lemma eval_dist_coe_append_left :
  ⁅(↑oa : oracle_comp (spec' ++ spec) α)⁆ = ⁅oa⁆ :=
stateless_oracle.eval_dist_simulate'_eq_eval_dist _ _ _ (λ i t, rfl)

/-- Coercing to an extra oracle on the left doesn't affect a computation's `prob_event`. -/
@[simp] lemma prob_event_coe_append_left (e : set α) :
  ⁅e | (↑oa : oracle_comp (spec' ++ spec) α)⁆ = ⁅e | oa⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_coe_append_left _ _ oa) e

end coe_append_left

section coe_append_right_of_coe

/-- Coerce an oracle and then append to the right. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default]
instance coe_append_right_of_coe (α) [has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)] :
  has_coe (oracle_comp coe_spec α) (oracle_comp (coe_spec' ++ spec) α) :=
{ coe := λ oa, ↑oa }

variables [has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)]
  (oa : oracle_comp coe_spec α)

lemma coe_append_right_of_coe.def : (↑oa : oracle_comp (coe_spec' ++ spec) α) =
  ↑(oa : oracle_comp coe_spec' α) := rfl

instance coe_append_right_of_coe.decidable [(↑oa : oracle_comp coe_spec' α).decidable] :
  (↑oa : oracle_comp (coe_spec' ++ spec) α).decidable :=
begin
  rw [coe_append_right_of_coe.def],
  refine @simulate'.decidable _ _ _ _ _ _ () _ _ (λ i t s, _),
  rw [stateless_oracle.apply_eq],
  apply_instance,
end

/-- Coercing to an extra oracle on the right doesn't affect a computation's `support`. -/
@[simp] lemma support_coe_append_right_of_coe :
  (↑oa : oracle_comp (coe_spec' ++ spec) α).support = (↑oa : oracle_comp coe_spec' α).support :=
by rw [coe_append_right_of_coe.def, support_coe_append_right]

/-- Coercing to an extra oracle on the right doesn't affect a computation's `fin_support`. -/
@[simp] lemma fin_support_coe_append_right_of_coe
  [oa.decidable] [(↑oa : oracle_comp coe_spec' α).decidable] :
  (↑oa : oracle_comp (coe_spec' ++ spec) α).fin_support =
    (↑oa : oracle_comp coe_spec' α).fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_coe_append_right_of_coe]

/-- Coercing to an extra oracle on the right doesn't affect a computation's `eval_dist`. -/
@[simp] lemma eval_dist_coe_append_right_of_coe :
  ⁅(↑oa : oracle_comp (coe_spec' ++ spec) α)⁆ = ⁅(↑oa : oracle_comp coe_spec' α)⁆ :=
stateless_oracle.eval_dist_simulate'_eq_eval_dist _ _ _ (λ i t, rfl)

/-- Coercing to an extra oracle on the right doesn't affect a computation's `prob_event`. -/
@[simp] lemma prob_event_coe_append_right_of_coe (e : set α) :
  ⁅e | (↑oa : oracle_comp (coe_spec' ++ spec) α)⁆ =
    ⁅e | (↑oa : oracle_comp coe_spec' α)⁆ :=
prob_event_eq_of_eval_dist_eq (eval_dist_coe_append_right_of_coe _ _ _ _) e

end coe_append_right_of_coe

section coe_right_side_append

/-- Coerce the oracle on the right side of an existing set of appended oracles. -/
@[priority std.priority.default+5]
instance coe_right_side_append (α)
  [∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)] :
  has_coe (oracle_comp (spec ++ coe_spec) α) (oracle_comp (spec ++ coe_spec') α) :=
{ coe := λ oa, oa.default_simulate' ⟪λ i, match i with
  | (sum.inl i') := (λ t, (query i' t : oracle_comp (spec ++ coe_spec') (spec.range i')))
  | (sum.inr i') := (λ t, (query i' t : oracle_comp (spec ++ coe_spec') (coe_spec.range i')))
end⟫ }

variables [∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)]
  (oa : oracle_comp (spec ++ coe_spec) α)

lemma coe_right_side_append.def : (↑oa : oracle_comp (spec ++ coe_spec') α) =
  oa.default_simulate' ⟪λ i, sum.rec_on i
    (λ i' t, (↑(query i' t) : oracle_comp (spec ++ coe_spec') (spec.range i')))
    (λ i' t, (query i' t : oracle_comp (spec ++ coe_spec') (coe_spec.range i')))⟫ :=
begin
  refine congr_arg (λ o, oa.default_simulate' ⟪o⟫) (funext $ λ i, _),
  cases i; refl
end

instance coe_right_side_append.decidable [oa.decidable]
  [h : ∀ α (oa' : oracle_comp coe_spec α) [oa'.decidable],
    (↑oa' : (oracle_comp coe_spec' α)).decidable] :
  (↑oa : oracle_comp (spec ++ coe_spec') α).decidable :=
begin
  rw [coe_right_side_append.def],
  refine @simulate'.decidable _ _ _ _ _ oa () _ _ (λ i t s, _),
  rw [stateless_oracle.apply_eq],
  cases i,
  { apply_instance },
  { exact @oracle_comp.decidable_bind _ _ _ _ _
      (@coe_append_left.decidable _ _ _ _ (h _ (query i t))) _ }
end

/-- If a coercion between two `oracle_spec`s preserves the `support` of oracle queries,
then the extended coercion with a left appended oracle also preserves the `support`.  -/
@[simp] lemma support_coe_right_side_append
  (h : ∀ i t, (↑(query i t : oracle_comp coe_spec (coe_spec.range i)) :
    oracle_comp coe_spec' (coe_spec.range i)).support = ⊤) :
  (↑oa : oracle_comp (spec ++ coe_spec') α).support = oa.support :=
begin
  rw [coe_right_side_append.def],
  refine stateless_oracle.support_simulate'_eq_support _ _ () (λ i t, _),
  cases i; simp only [coe_coe, support_coe_append_left, support_coe_append_right,
    support_query, set.top_eq_univ, h]
end

end coe_right_side_append

section coe_left_side_append

/-- Coerce the oracle on the left side of an existing set of appended oracles -/
@[priority std.priority.default+4]
instance coe_left_side_append (α)
  [∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)] :
  has_coe (oracle_comp (coe_spec ++ spec) α) (oracle_comp (coe_spec' ++ spec) α) :=
{ coe := λ oc, oc.simulate' ⟪λ i, match i with
| (sum.inl i') := (λ t, (query i' t : oracle_comp (coe_spec' ++ spec) (coe_spec.range i')))
| (sum.inr i') := (λ t, (query i' t : oracle_comp (coe_spec' ++ spec) (spec.range i')))
end⟫ () }

end coe_left_side_append

section coe_append_assoc

/-- Coerce towards a standardized append ordering (matching the `infixl` declaration for `++`) -/
@[priority std.priority.default+50]
instance coe_append_assoc (α) :
  has_coe (oracle_comp (spec ++ (spec' ++ spec'')) α) (oracle_comp (spec ++ spec' ++ spec'') α) :=
⟨λ oc, oc.simulate' ⟪λ i, match i with 
| (sum.inl i) := let i' : (spec ++ spec' ++ spec'').ι := sum.inl (sum.inl i) in query i'
| (sum.inr (sum.inl i)) := let i' : (spec ++ spec' ++ spec'').ι := sum.inl (sum.inr i) in query i'
| (sum.inr (sum.inr i)) := let i' : (spec ++ spec' ++ spec'').ι := sum.inr i in query i'
end⟫ ()⟩

end coe_append_assoc

section examples

-- This set of examples serves as sort of a "unit test" for the coercions above
variable [∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)]

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

end oracle_comp