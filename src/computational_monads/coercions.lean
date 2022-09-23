import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.constructions.identity_oracle

/-!
# Coercions Between Computations With Different Oracle Access

This file provides a number of `has_coe` instances for different `oracle_comp` computations.

The main coercions are for the append operation on `oracle_spec`,
  allowing an increase the number of oracles in a number of ways.
This allows a computation to be written by composing computations using fewer oracles.

The coercions are ordered very specifically using priority attributes,
  to ensure that they can converge to anything in a sort of 'standard form'
In particular, can coerce to any set of appended oracles assuming that:
1. The target oracle list is fully left associated, which is the same associativity as `++`.
2. The subset of original oracles in the target is in the same order.

To match this we adopt both conventions in general, and use a standard ordering for all oracles.
In particular we start with the basic finite oracles: `coin_oracle ++ uniform_selecting ++ ...`,
  and then add additional oracles further in the list. This standard ordering allows most coercions
  between oracles to happen automatically
-/

open oracle_comp oracle_spec distribution_semantics 

variables (spec spec' spec'' spec''' : oracle_spec)
  (coe_spec coe_spec' coe_spec'' coe_spec''' : oracle_spec) {α : Type}

section uniform_select

/-- coerce a coin flip into a uniform random selection of a `bool` -/
noncomputable instance coe_coin_uniform_select (α) :
  has_coe (oracle_comp coin_oracle α) (oracle_comp uniform_selecting α) :=
{ coe := λ oa, oa.default_simulate' ⟪λ _ _, $ᵗ bool⟫ }

noncomputable example : oracle_comp uniform_selecting bool :=
do {b ← coin, b' ←$ᵗ bool, return (band b b')}

lemma coe_coin_uniform_select_def (oa : oracle_comp coin_oracle α) :
  (↑oa : oracle_comp uniform_selecting α) = oa.default_simulate' ⟪λ _ _, $ᵗ bool⟫ := rfl

/-- Coercing to a `uniform_selecting` oracle doesn't change the underlying distribution -/
@[simp]
lemma coe_coin_uniform_select_equiv_coin : Π {α : Type} (oc : oracle_comp coin_oracle α),
    (↑oc : oracle_comp uniform_selecting α) ≃ₚ oc
| _ (pure' α a) := by simp [coe_coin_uniform_select_def, pmf.pure_map]
| _ (bind' α β oa ob) := begin
  rw [coe_coin_uniform_select_def],
  refine (stateless_oracle.simulate'_query_equiv_of_equiv _ _ _ _),
  intros i t,
  exact eval_dist_uniform_select_fintype bool,
end
| _ (query i t) := begin
  erw [coe_coin_uniform_select_def, simulate'_query_equiv, stateless_oracle.apply_eq,
    fst_map_bind_mk_equiv, map_id_equiv],
  exact eval_dist_uniform_select_fintype bool,
end

end uniform_select

section coe_append

section coe_append_right

/-- Coerce a computation to one with access to another oracle on the right,
  forwarding the old queries to the left side of the combined set of oracles -/
@[priority std.priority.default-50]
instance coe_append_right (α) : has_coe (oracle_comp spec α) (oracle_comp (spec ++ spec') α) :=
{ coe := default_simulate' ⟪λ i, let i' : (spec ++ spec').ι := sum.inl i in query i'⟫ }

-- TODO: other versions of this
lemma coe_append_right_def (oa : oracle_comp spec α) : (↑oa : oracle_comp (spec ++ spec') α) =
  oa.default_simulate' ⟪λ i t, let i' : (spec ++ spec').ι := sum.inl i in query i' t⟫ := rfl

@[simp]
lemma support_coe_append_right (oa : oracle_comp spec α) :
  (↑oa : oracle_comp (spec ++ spec') α).support = oa.support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { simp only [coe_append_right_def, default_simulate'_return, support_map,
      support_return, set.image_singleton], },
  { simp_rw [coe_append_right_def] at hoa hob,
    simp_rw [support_bind, coe_append_right_def,
      stateless_oracle.support_default_simulate'_bind, hoa, hob] },
  { rw [coe_append_right_def, stateless_oracle.support_default_simulate'_query,
      support_query, support_query] },
end

section distribution_semantics

lemma coe_append_right_pure_equiv [spec.finite_range] [spec'.finite_range] (a : α) :
  (↑(pure a : oracle_comp spec α) : oracle_comp (spec ++ spec') α)
    ≃ₚ (pure a : oracle_comp (spec ++ spec') α) :=
default_simulate'_pure_equiv _ a

/-- The right hand simulation oracle is irrelevent to simulate an append right coercion -/
lemma simulate'_coe_append_right_equiv [spec.finite_range] [spec'.finite_range]
  [spec''.finite_range] (oa : oracle_comp spec α) (so : simulation_oracle spec spec'')
  (so' : simulation_oracle spec' spec'') (s : so.S × so'.S) :
  simulate' (so ++ₛ so') ↑oa s ≃ₚ simulate' so oa s.1 :=
begin
  induction oa with α a α β oa ob i t,
  { sorry },
  { sorry },
  { sorry }
end

lemma simulate_coe_append_right_equiv [spec''.finite_range] (oa : oracle_comp spec α)
  (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec'') (s : so.S × so'.S) :
  simulate (so ++ₛ so') ↑oa s ≃ₚ do { ⟨a, s'⟩ ← simulate so oa s.1, pure (a, s', s.2) } :=
sorry

end distribution_semantics

end coe_append_right

section coe_append_left

/-- Coerce a computation to one with access to another oracle on the left,
  forwarding the old queries to the left side of the combined set of oracles -/
@[priority std.priority.default-50]
instance coe_append_left (α) : has_coe (oracle_comp spec α) (oracle_comp (spec' ++ spec) α) :=
{ coe := default_simulate' ⟪λ i, let i' : (spec' ++ spec).ι := sum.inr i in query i'⟫ }

end coe_append_left

section coe_append_right_of_coe

/-- Coerce an oracle and then append to the right. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default]
instance coe_append_right_of_coe (α) [has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)] :
  has_coe (oracle_comp coe_spec α) (oracle_comp (coe_spec' ++ spec) α) :=
{ coe := λ oa, ↑oa }

end coe_append_right_of_coe

section coe_right_side_append

/-- Coerce the oracle on the right side of an existing set of appended oracles -/
@[priority std.priority.default+5]
instance coe_right_side_append (α) [∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)] :
  has_coe (oracle_comp (spec ++ coe_spec) α) (oracle_comp (spec ++ coe_spec') α) :=
{ coe := λ oc, oc.default_simulate' ⟪λ i, match i with
  | (sum.inl i') := (λ t, (query i' t : oracle_comp (spec ++ coe_spec') (spec.range i')))
  | (sum.inr i') := (λ t, (query i' t : oracle_comp (spec ++ coe_spec') (coe_spec.range i')))
end ⟫ }

end coe_right_side_append

section coe_left_side_append

/-- Coerce the oracle on the left side of an existing set of appended oracles -/
@[priority std.priority.default+5]
instance coe_left_side_append (α) [∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)] :
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
variable [h : ∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)]
include h

-- coerce a single `coin_oracle` and then append extra oracles
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
noncomputable example {spec : oracle_spec} : oracle_comp (uniform_selecting ++ spec) bool := 
do { n ←$[0..10], if n ≤ 3 then return ff else coin }

end examples

end coe_append

section coe_simulation_oracle

/-- Use a coercion on the resulting type of a simulation to coerce the simulation oracle itself.
  This allows for greater flexibility when specifying the simulation oracle when
    both the initial and final `oracle_spec` are some appended set of oracles -/
instance [∀ α, has_coe (oracle_comp coe_spec α) (oracle_comp coe_spec' α)] :
  has_coe (simulation_oracle spec coe_spec) (simulation_oracle spec coe_spec') :=
{ coe := λ so, { S := so.S, default_state := so.default_state, o := λ i x, ↑(so.o i x) } }

/-- Coerce a simulation oracle to include an additional number of resulting oracles -/
example (so : simulation_oracle coe_spec coe_spec') :
  simulation_oracle coe_spec (coe_spec' ++ spec ++ spec') := ↑so

/-- Can use coercions to seperately simulate both sides of appended oracle specs -/
example (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec''') :
  simulation_oracle (spec ++ spec') (spec'' ++ spec''') :=
↑so ++ₛ ↑so'

end coe_simulation_oracle