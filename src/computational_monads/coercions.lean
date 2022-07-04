import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulation_oracles

/-!
# Coercions Between Computations With Different Oracle Access

This file provides a number of `has_coe` instances for different `oracle_comp` computations.

The main coercions are for the append operation on `oracle_spec`,
  allowing an increase the number of oracles in a number of ways.
This allows a computation to be written by composing computations using fewer oracles.
-/

open oracle_comp oracle_spec

variables (A B : Type) (spec spec' spec'' spec''' : oracle_spec)
  (coe_spec coe_spec' coe_spec'' coe_spec''' : oracle_spec)

section uniform_select

/-- coerce a coin flip into a uniform random selection of a `bool` -/
noncomputable instance coe_coin_uniform_select :
  has_coe (oracle_comp coin_oracle A) (oracle_comp uniform_selecting A) :=
{ coe := λ oa, oa.simulate' ⟪λ _ _, $ᵗ bool⟫ () }

noncomputable example : oracle_comp uniform_selecting bool :=
do {b ← coin, b' ←$ᵗ bool, return (band b b')}

lemma coe_coin_uniform_select_def (oa : oracle_comp coin_oracle A) :
  (↑oa : oracle_comp uniform_selecting A) = oa.simulate' ⟪λ _ _, $ᵗ bool⟫ () := rfl

@[simp]
lemma coe_coin_uniform_select_equiv_coin :
  Π {A : Type} (oc : oracle_comp coin_oracle A),
    (↑oc : oracle_comp uniform_selecting A) ≃ₚ oc
| _ (pure' A a) := by simp [coe_coin_uniform_select_def, pmf.pure_map]
| _ (bind' A B oa ob) := begin
  rw [coe_coin_uniform_select_def],
end
| _ (query i t) := sorry

end uniform_select

section coe_append

instance coe_append_right :
  has_coe (oracle_comp spec A) (oracle_comp (spec ++ spec') A) :=
{ coe := λ oc, oc.default_simulate' ⟪λ i t, let i' : (spec ++ spec').ι := sum.inl i in query i' t⟫ }

instance coe_append_left :
  has_coe (oracle_comp spec A) (oracle_comp (spec' ++ spec) A) :=
{ coe := λ oc, oc.simulate'
    ⟪ (λ i t, let i' : (spec' ++ spec).ι := sum.inr i in query i' t) ⟫ () }

instance coe_right_side_append [∀ A, has_coe (oracle_comp coe_spec A) (oracle_comp coe_spec' A)] :
  has_coe (oracle_comp (spec ++ coe_spec) A) (oracle_comp (spec ++ coe_spec') A) :=
{ coe := λ oc, oc.simulate' ⟪λ i, sum.rec
    (λ i' t, (query i' t : oracle_comp (spec ++ coe_spec') (spec.range i')))
    (λ i' t, (query i' t : oracle_comp (spec ++ coe_spec') (coe_spec.range i')))
  i⟫ () }

instance coe_left_side_append [∀ A, has_coe (oracle_comp coe_spec A) (oracle_comp coe_spec' A)] :
  has_coe (oracle_comp (coe_spec ++ spec) A) (oracle_comp (coe_spec' ++ spec) A) :=
{ coe := λ oc, oc.simulate' ⟪λ i, sum.rec
    (λ i' t, (query i' t : oracle_comp (coe_spec' ++ spec) (coe_spec.range i')))
    (λ i' t, (query i' t : oracle_comp (coe_spec' ++ spec) (spec.range i')))
  i⟫ () }

instance coe_both_sides_append [∀ A, has_coe (oracle_comp coe_spec A) (oracle_comp coe_spec' A)]
  [∀ A, has_coe (oracle_comp coe_spec'' A) (oracle_comp coe_spec''' A)] :
  has_coe (oracle_comp (coe_spec ++ coe_spec'') A) (oracle_comp (coe_spec' ++ coe_spec''') A) :=
{ coe := λ oc, oc.simulate' ⟪λ i, sum.rec
    (λ i' t, (query i' t : oracle_comp (coe_spec' ++ coe_spec''') (coe_spec.range i')))
    (λ i' t, (query i' t : oracle_comp (coe_spec' ++ coe_spec''') (coe_spec''.range i')))
  i⟫ () }

instance coe_append_right_of_coe [has_coe (oracle_comp coe_spec A) (oracle_comp coe_spec' A)] :
  has_coe (oracle_comp coe_spec A) (oracle_comp (coe_spec' ++ spec'') A) :=
{ coe := coe }

instance coe_append_left_of_coe [has_coe (oracle_comp coe_spec A) (oracle_comp coe_spec' A)] :
  has_coe (oracle_comp coe_spec A) (oracle_comp (spec'' ++ coe_spec') A) :=
{ coe := coe }

@[priority 1001]
instance coe_append_assoc :
  has_coe (oracle_comp (spec ++ (spec' ++ spec'')) A) (oracle_comp (spec ++ spec' ++ spec'') A) :=
⟨λ oc, oc.simulate' ⟪λ i, match i with 
| (sum.inl i) :=
    λ t, let i' : (spec ++ spec' ++ spec'').ι := sum.inl (sum.inl i) in query i' t
| (sum.inr (sum.inl i)) :=
    λ t, let i' : (spec ++ spec' ++ spec'').ι := sum.inl (sum.inr i) in query i' t
| (sum.inr (sum.inr i)) := 
    λ t, let i' : (spec ++ spec' ++ spec'').ι := sum.inr i in query i' t
end⟫ ()⟩

section examples

variable [h : ∀ A, has_coe (oracle_comp coe_spec A) (oracle_comp coe_spec' A)]
include h

-- This set of examples serves as sort of a "unit test" for the coercions above

-- coerce a single `coin_oracle` and then append extra oracles
example (oa : oracle_comp coe_spec A) :
  oracle_comp (coe_spec' ++ spec' ++ spec'') A := ↑oa
example (oa : oracle_comp coe_spec A) :
  oracle_comp (spec ++ coe_spec' ++ spec') A := ↑oa
example (oa : oracle_comp coe_spec A) :
  oracle_comp (spec ++ spec' ++ coe_spec') A := ↑oa

-- coerce left side of append and then append on additional oracles
example (oa : oracle_comp (coe_spec ++ spec) A) :
  oracle_comp (coe_spec' ++ spec ++ spec') A := ↑oa
example (oa : oracle_comp (coe_spec ++ spec) A) :
  oracle_comp (coe_spec' ++ spec' ++ spec) A := ↑oa
example (oa : oracle_comp (coe_spec ++ spec) A) :
  oracle_comp (spec' ++ coe_spec' ++ spec) A := ↑oa

-- coerce right side of append and then append on additional oracles
example (oa : oracle_comp (spec ++ coe_spec) A) :
  oracle_comp (spec ++ coe_spec' ++ spec') A := ↑oa
example (oa : oracle_comp (spec ++ coe_spec) A) :
  oracle_comp (spec ++ spec' ++ coe_spec') A := ↑oa
example (oa : oracle_comp (spec ++ coe_spec) A) :
  oracle_comp (spec' ++ spec ++ coe_spec') A := ↑oa

-- coerce an inside part while also applying associativity
example (oa : oracle_comp (spec ++ (spec' ++ coe_spec)) A) :
  oracle_comp (spec ++ spec' ++ coe_spec') A := ↑oa
example (oa : oracle_comp (spec ++ (coe_spec ++ spec')) A) :
  oracle_comp (spec ++ coe_spec' ++ spec') A := ↑oa
example (oa : oracle_comp (coe_spec ++ (spec ++ spec')) A) :
  oracle_comp (coe_spec' ++ spec ++ spec') A := ↑oa

end examples

end coe_append

/-- coercion makes it possible to mix computations on individual oracles -/
noncomputable example {spec : oracle_spec} : oracle_comp (uniform_selecting ++ spec) bool := 
do { n ←$[0..10], if n = 0 then return ff else coin }