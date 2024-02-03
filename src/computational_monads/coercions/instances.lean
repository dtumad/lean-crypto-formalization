/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.sub_spec
import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.oracle_append

/-!
# Sub-Spec Instances for Common Sets of Oracles

This file defines `is_sub_spec` instances for common coercions.
The first is a coercion from `empty_spec` to any other `oracle_spec` (since there are no queries).
Another is a simple coercion from `coin_spec` to `unif_spec`,
by selecting the coin result from a uniform selection between `0` and `1`.

We also define a number of coercions involving append.
These instances allow an `oracle_spec` of the form `spec₁ ++ ... ++ spec₂`
to coerce to one of the form `spec'₁ ++ ... ++ spec'₂`, assuming that
the set of oracles in the first is a sub-sequence of the oracles in the second.
We also include associativity instances, so parenthisization of the sequence is irrelevant.

Note that this requires the ordering of oracles in each to match,
and so we generally adopt a standard ordering of `oracle_spec` for computations
in order to make this apply as often as possible. We specifically adopt the following convention:
  `{coin_oracle} ++ {unif_spec} ++ {random oracle} ++ {adversary oracles} ++ ...`,
where any of the individual parts may be ommited. The adversary oracles are for
things like a signing oracle in unforgeability experiments of a signature scheme.

The typelcasses are applied in an order defined by specific priorities:
1. Try applying the associativity instance to remove parenthesization.
2. If both the subspec and superspec are an append, try to independently coerce both sides.
3. Try to coerce the subspec to the left side of the superspec append.
4. Try to coerce the subspec to the right side of the superspec append.
5. Try appending a single oracle to the left side of the subspec.
6. Try appending a single oracle to the right side of the subspec.
7. Try coercing the subspec to itself.
This ordering is chosen to both give a generally applicable instance tree,
and avoid an infinite typeclass search whether or not an instance exists.
-/

namespace oracle_spec

open oracle_comp

variables {spec spec' spec'' : oracle_spec} {α β γ S S' : Type}

section empty_spec

/-- Coerce a computation with no oracles to one with any potential set of oracles. -/
@[priority std.priority.default+101]
instance is_sub_spec_empty_spec (spec : oracle_spec) : is_sub_spec ∅ spec :=
{ to_fun := λ i, empty.elim i,
  to_fun_equiv := λ i, empty.elim i }

@[simp] lemma is_sub_spec_empty_spec_apply (spec : oracle_spec) (i : empty) (t : unit) :
  (oracle_spec.is_sub_spec_empty_spec spec).to_fun i t = return default := i.elim

end empty_spec

section coin_spec_unif_spec

/-- Coerce a coin flip into a uniform random selection of a `bool`.
Use uniform selection from the vector `[tt, ff]` to get constructiveness. -/
@[priority std.priority.default+100]
noncomputable instance is_sub_spec_coin_spec_unif_spec : is_sub_spec coin_spec unif_spec :=
{ to_fun := λ i t, $ᵗ bool,
  to_fun_equiv := λ i t, symm ((query_dist_equiv_iff i t _).2
    (λ u u', by cases u; cases u'; simp [prob_output_uniform_select_fintype bool])) }

@[simp] lemma is_sub_spec_coin_unif_spec_apply (i t : unit) :
  (oracle_spec.is_sub_spec_coin_spec_unif_spec).to_fun i t = $ᵗ bool := rfl

@[simp] lemma coe_coin_unif_spec :
  (↑coin : oracle_comp unif_spec bool) = $ᵗ bool := rfl

end coin_spec_unif_spec

section append_left

/-- Coerce a computation to one with access to another oracle on the left,
forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default]
instance is_sub_spec_append_left (spec spec' : oracle_spec) : spec ⊂ₒ (spec' ++ spec) :=
{ to_fun := λ i t, @query (spec' ++ spec) (sum.inr i) t,
  to_fun_equiv := λ i t, trans (eval_dist_query (sum.inr i) t) (eval_dist_query i t).symm }

@[simp] lemma is_sub_spec_append_left_apply (i : spec.ι) (t : spec.domain i) :
  (oracle_spec.is_sub_spec_append_left spec spec').to_fun i t =
    @query (spec' ++ spec) (sum.inr i) t := rfl

variables (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S')

@[simp] lemma simulate_coe_append_left (s : S × S') (oa : oracle_comp spec' α) :
  simulate (so ++ₛₒ so') ↑oa s = (λ (x : α × S'), (x.1, s.1, x.2)) <$> simulate so' oa s.2 :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { simp only [coe_sub_spec_return, simulate_return, map_pure, prod.mk.eta] },
  { simp [hoa, bind_assoc, oracle_comp.map_eq_bind_return_comp] }
end

@[simp] lemma simulate'_coe_append_left (s : S × S') (oa : oracle_comp spec' α) :
  (simulate' (so ++ₛₒ so') ↑oa s) = simulate' so' oa s.2 :=
by simp [simulate'.def]

end append_left

section append_right

/-- Coerce a computation to one with access to another oracle on the right,
forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default+1]
instance is_sub_spec_append_right (spec spec' : oracle_spec) : spec ⊂ₒ (spec ++ spec') :=
{ to_fun := λ i t, @query (spec ++ spec') (sum.inl i) t,
  to_fun_equiv := λ i t, trans (eval_dist_query (sum.inl i) t) (eval_dist_query i t).symm }

@[simp] lemma is_sub_spec_append_right_apply {spec spec' : oracle_spec}
  (i : spec.ι) (t : spec.domain i) : (oracle_spec.is_sub_spec_append_right spec spec').to_fun i t =
    @query (spec ++ spec') (sum.inl i) t := rfl

variables (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S')

@[simp] lemma simulate_coe_append_right (s : S × S') (oa : oracle_comp spec α) :
  simulate (so ++ₛₒ so') ↑oa s = (λ (x : α × S), (x.1, x.2, s.2)) <$> simulate so oa s.1 :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { simp only [coe_sub_spec_return, simulate_return, map_pure, prod.mk.eta] },
  { simp [hoa, bind_assoc, oracle_comp.map_eq_bind_return_comp] }
end

@[simp] lemma simulate'_coe_append_right (s : S × S') (oa : oracle_comp spec α) :
  (simulate' (so ++ₛₒ so') ↑oa s) = simulate' so oa s.1 :=
by simp [simulate'.def]

end append_right

section append_left_of_is_subspec

/-- Coerce an oracle and then append to the left. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default+10]
instance is_sub_spec_append_left_of_is_sub_spec
  (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec sub_spec (spec ++ super_spec) :=
{ to_fun := λ i t, ↑(h.to_fun i t),
  to_fun_equiv := λ i t, (eval_dist_coe_sub_spec _ _ _).trans (is_sub_spec.to_fun_equiv _ _) }

end append_left_of_is_subspec

section append_right_of_is_subspec

/-- Coerce an oracle and then append to the right. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default+11]
instance is_sub_spec_append_right_of_is_sub_spec
  (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec sub_spec (super_spec ++ spec) :=
{ to_fun := λ i t, ↑(h.to_fun i t),
  to_fun_equiv := λ i t, (eval_dist_coe_sub_spec _ _ _).trans (is_sub_spec.to_fun_equiv _ _) }

end append_right_of_is_subspec

section left_side_append

/-- Coerce the oracle on the right side of an existing set of appended oracles. -/
@[priority std.priority.default+20]
instance is_sub_spec_left_side_append
  (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec (sub_spec ++ spec) (super_spec ++ spec) :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, (append.range_inl sub_spec spec i).symm.rec (h.to_fun i t)
  | (sum.inr i) := λ t, @query (super_spec ++ _) (sum.inr i) t
  end,
  to_fun_equiv := λ i, match i with
  | (sum.inl i) := λ t, (eval_dist_coe_sub_spec _ _ (h.to_fun i t)).trans
      ((h.to_fun_equiv i t).trans (by exact rfl))
  | (sum.inr i) := λ t, rfl
  end }

end left_side_append

section right_side_append

/-- Coerce the oracle on the right side of an existing set of appended oracles. -/
@[priority std.priority.default+21]
instance is_sub_spec_right_side_append (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec (spec ++ sub_spec) (spec ++ super_spec) :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, @query (_ ++ super_spec) (sum.inl i) t
  | (sum.inr i) := λ t, (append.range_inr spec sub_spec i).symm.rec (h.to_fun i t)
  end,
  to_fun_equiv := λ i, match i with
  | (sum.inl i) := λ t, rfl
  | (sum.inr i) := λ t, (eval_dist_coe_sub_spec _ _ (h.to_fun i t)).trans
      ((h.to_fun_equiv i t).trans (by exact rfl))
  end }

end right_side_append

section assoc

/-- Coerce towards a standardized append ordering (matching the `infixl` declaration for `++`) -/
@[priority std.priority.default+30]
instance is_sub_spec_assoc (spec spec' spec'' : oracle_spec) :
  is_sub_spec (spec ++ (spec' ++ spec'')) (spec ++ spec' ++ spec'') :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, @query (spec ++ spec' ++ spec'') (sum.inl (sum.inl i)) t
  | (sum.inr (sum.inl i)) := λ t, @query (spec ++ spec' ++ spec'') (sum.inl (sum.inr i)) t
  | (sum.inr (sum.inr i)) := λ t, @query (spec ++ spec' ++ spec'') (sum.inr i) t
  end,
  to_fun_equiv := λ i, match i with
  | (sum.inl i) := λ t, rfl
  | (sum.inr (sum.inl i)) := λ t, rfl
  | (sum.inr (sum.inr i)) := λ t, rfl
  end }

end assoc

end oracle_spec

namespace oracle_spec

open oracle_comp

section examples

-- This set of examples serves as sort of a "unit test" for the coercions above
variables (α : Type) (spec spec' spec'' spec''' : oracle_spec)
  (coe_spec coe_spec' : oracle_spec)
  [coe_spec ⊂ₒ coe_spec']

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
noncomputable example {spec : oracle_spec} : oracle_comp (unif_spec ++ spec) bool :=
do { n ←$[0..3141], b ← coin, if n ≤ 1618 ∧ b = tt then return ff else coin }

-- TODO!!!: does this work ever without deep recursion? probably not?
-- example (oa : prob_comp ∅ α) : oracle_comp unif_spec α := ↑oa

end examples

end oracle_spec