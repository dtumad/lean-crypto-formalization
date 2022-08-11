import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.oracle_append
import computational_monads.simulation_semantics.constructions.stateless_oracle
import computational_monads.simulation_semantics.constructions.identity_oracle

/-!
# Coercions Between Computations With Different Oracle Access

This file provides a number of `has_coe` instances for different `oracle_comp` computations.

The main coercions are for the append operation on `oracle_spec`,
  allowing an increase the number of oracles in a number of ways.
This allows a computation to be written by composing computations using fewer oracles.
-/

open oracle_comp oracle_spec distribution_semantics

-- TODO: α β γ
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

/-- Coercing to a `uniform_selecting` oracle doesn't change the underlying distribution -/
@[simp]
lemma coe_coin_uniform_select_equiv_coin :
  Π {A : Type} (oc : oracle_comp coin_oracle A),
    (↑oc : oracle_comp uniform_selecting A) ≃ₚ oc
| _ (pure' A a) := by simp [coe_coin_uniform_select_def, pmf.pure_map]
| _ (bind' A B oa ob) := begin
  rw [coe_coin_uniform_select_def],
  refine (stateless_oracle.simulate'_query_equiv_of_equiv _ _ _ _),
  intros i t,
  exact eval_distribution_uniform_select_fintype bool,
end
| _ (query i t) := begin
  erw [coe_coin_uniform_select_def, simulate'_query_equiv, stateless_oracle.apply,
    fst_map_bind_mk_equiv, map_id_equiv],
  exact eval_distribution_uniform_select_fintype bool,
end

end uniform_select

section coe_append

/-- Coerce a computation to one with access to another oracle on the right,
  forwarding the old queries to the left side of the combined set of oracles -/
instance coe_append_right :
  has_coe (oracle_comp spec A) (oracle_comp (spec ++ spec') A) :=
{ coe := default_simulate' ⟪λ i t, let i' : (spec ++ spec').ι := sum.inl i in query i' t⟫ }

-- TODO: other versions of this
lemma coe_append_right_def (oa : oracle_comp spec A) : (↑oa : oracle_comp (spec ++ spec') A) =
  oa.default_simulate' ⟪λ i t, let i' : (spec ++ spec').ι := sum.inl i in query i' t⟫ := rfl

lemma coe_append_right_pure_equiv [spec.finite_range] [spec'.finite_range] (a : A) :
  (↑(pure a : oracle_comp spec A) : oracle_comp (spec ++ spec') A)
    ≃ₚ (pure a : oracle_comp (spec ++ spec') A) :=
default_simulate'_pure_equiv _ a

lemma simulate_coe_append_right_equiv [spec''.finite_range] (oa : oracle_comp spec A)
  (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec'') (s : so.S × so'.S) :
  simulate (so ++ₛ so') ↑oa s ≃ₚ do { ⟨a, s'⟩ ← simulate so oa s.1, pure (a, s', s.2) } :=
sorry

lemma simulate'_coe_append_right_equiv [spec.finite_range] [spec'.finite_range] [spec''.finite_range]
  (oa : oracle_comp spec A)
  (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec'') (s : so.S × so'.S) :
  simulate' (so ++ₛ so') ↑oa s ≃ₚ simulate' so oa s.1 :=
begin
  induction oa with A a A B oa ob i t,
  {
    
    simp only [pure'_eq_pure, simulate'_pure, map_pure_equiv, eval_distribution_return],
    refine trans (simulate'_map_equiv _ _ _ _) _,
    rw [simulate_pure, simulate'_pure, map_map_pure_equiv],
    refl,
  },
  {
    sorry,
  },
  {
    sorry,
  }
end

-- lemma simulate_coe_append_right (oa : oracle_comp spec A) (so : simulation_oracle spec spec')
--   (s : so.S × unit) :
--   (simulate' (so +++ₛ (identity_oracle spec'')) (↑oa : oracle_comp (spec ++ spec'') A) s) =
--     ↑(simulate' so oa s.1) :=
-- sorry

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

-- This set of examples serves as sort of a "unit test" for the coercions above
variable [h : ∀ A, has_coe (oracle_comp coe_spec A) (oracle_comp coe_spec' A)]
include h

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
do { n ←$[0..10], if n ≤ 3 then return ff else coin }

section coe_simulation_oracle

/-- Use a coercion on the resulting type of a simulation to coerce the simulation oracle itself.
  This allows for greater flexibility when specifying the simulation oracle when
    both the initial and final `oracle_spec` are some appended set of oracles -/
instance {spec spec' spec'' : oracle_spec}
  [∀ α, has_coe (oracle_comp spec' α) (oracle_comp spec'' α)] :
  has_coe (simulation_oracle spec spec') (simulation_oracle spec spec'') :=
{ coe := λ so, { S := so.S, default_state := so.default_state, o := λ i x, ↑(so.o i x) } }

example (so : simulation_oracle spec spec') :
  simulation_oracle spec (spec ++ spec' ++ spec'') := ↑so

/-- Can use coercions to seperately simulate both sides of appended oracle specs -/
example (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec''') :
  simulation_oracle (spec ++ spec') (spec'' ++ spec''') :=
↑so ++ₛ ↑so'

end coe_simulation_oracle