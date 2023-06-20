/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.prod

/-!
# Oracle Simulation Semantics

Defines the notion of simulating a computation by defining the outputs of oracle query.
A method of simulation is given by `sim_oracle`, which contains an internal state
  as well as a function to return a value and update the state given a query to the oracle.

It also contains a `default_state`, specifying the value to use for the default oracle state.
For example a logging query would use an empty log as the default state.

We define `simulate'` to be simulation followed by discarding the state.
This is useful for things like a random oracle, where the final log isn't relevant in general.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation.
`default_state` can be provided as a standard initial state for simulation (`default_simulate`). -/
structure sim_oracle (spec spec' : oracle_spec) (S : Type) :=
(default_state : S)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

namespace sim_oracle

/-- Example of an oracle maintaining in internal incrementing value,
  and returning a fake coin flip based on whether the state is even. -/
example : sim_oracle oracle_spec.coin_spec oracle_spec.coin_spec ℕ :=
{ default_state := 0,
  o := λ i ⟨t, n⟩, return (if even n then tt else ff, n + 1) }

/-- View a simulation oracle as a function corresponding to the internal oracle `o` -/
instance has_coe_to_fun : has_coe_to_fun (sim_oracle spec spec' S)
  (λ so, Π (i : spec.ι), spec.domain i × S → oracle_comp spec' (spec.range i × S)) :=
{ coe := λ so, so.o }

lemma has_coe_to_fun.def (so : sim_oracle spec spec' S) (i : spec.ι)
  (x : spec.domain i × S) : so i x = so.o i x := rfl

def inhabited_state (so : sim_oracle spec spec' S) : inhabited S := ⟨so.default_state⟩

instance inhabited [inhabited S] : inhabited (sim_oracle spec spec' S) :=
⟨{default_state := default, o := λ _ _, return default}⟩

end sim_oracle

namespace oracle_comp

open_locale big_operators ennreal
open oracle_spec

variables (so : sim_oracle spec spec' S) (a : α) (i : spec.ι) (t : spec.domain i)
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (f : α → β) (s : S) (x : α) (e : set α)

section simulate

/-- Simulate an oracle comp to an oracle comp with a different spec.
Requires providing a maximum recursion depth for the `repeat` constructor. -/
def simulate {spec spec' : oracle_spec} (so : sim_oracle spec spec' S) :
  Π {α : Type} (oa : oracle_comp spec α), S → oracle_comp spec' (α × S)
| _ (pure' α a) state := return ⟨a, state⟩
| _ (bind' α β oa ob) state := simulate oa state >>= λ x, simulate (ob x.1) x.2
| _ (query i t) state := so i (t, state)

/-- Convenience definition to use the default state as the initial state for `simulate`.
Marked to be reduced and inlined, so the definition is essentially just notation. -/
@[inline, reducible, simp]
def default_simulate (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' (α × S) := simulate so oa so.default_state

@[simp] lemma simulate_return : simulate so (return a) s = return (a, s) := rfl

@[simp] lemma simulate_bind : simulate so (oa >>= ob) s =
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp] lemma simulate_query : simulate so (query i t) s = so i (t, s) := rfl

@[simp] lemma simulate_map : simulate so (f <$> oa) s = prod.map f id <$> simulate so oa s := rfl

end simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
def simulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S) :
  oracle_comp spec' α := prod.fst <$> oa.simulate so s

/-- Convenience definition to use the default state as the initial state for `simulate'`.
Marked to be reduced and inlined, so the definition is essentially just notation. -/
@[inline, reducible, simp]
def default_simulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' α := oa.simulate' so so.default_state

lemma simulate'_def : simulate' so oa s = prod.fst <$> oa.simulate so s := rfl

-- TODO: these should have a special simp category, to not be eagerly applied
@[simp] lemma simulate'_return : simulate' so (return a) s = prod.fst <$> (return (a, s)) := rfl

lemma simulate'_pure' : simulate' so (pure' α a) s = prod.fst <$> (return (a, s)) := rfl

lemma simulate'_pure : simulate' so (pure a) s = prod.fst <$> (return (a, s)) := rfl

@[simp] lemma simulate'_bind : simulate' so (oa >>= ob) s =
  prod.fst <$> (simulate so oa s >>= λ x, simulate so (ob x.1) x.2) := rfl

lemma simulate'_bind' : simulate' so (bind' α β oa ob) s =
  prod.fst <$> (simulate so oa s >>= λ x, simulate so (ob x.1) x.2) := rfl

@[simp] lemma simulate'_query : simulate' so (query i t) s = prod.fst <$> so i (t, s) := rfl

@[simp] lemma simulate'_map : simulate' so (f <$> oa) s =
  prod.fst <$> (prod.map f id <$> simulate so oa s) := rfl

@[simp] lemma support_simulate' : (simulate' so oa s).support =
  prod.fst '' (simulate so oa s).support := by simp only [simulate', support_map]

lemma mem_support_simulate'_iff_exists_state (x : α) :
  x ∈ (simulate' so oa s).support ↔ ∃ (s' : S), (x, s') ∈ (simulate so oa s).support :=
by simp only [support_simulate', set.mem_image, prod.exists,
  exists_and_distrib_right, exists_eq_right]

@[simp] lemma eval_dist_simulate' : ⁅simulate' so oa s⁆ = ⁅simulate so oa s⁆.map prod.fst :=
eval_dist_map _ prod.fst

/-- Express the probability of `simulate'` returning a specific value
as the sum over all possible output states of the probability of `simulate` return it -/
theorem prob_output_simulate' : ⁅= x | simulate' so oa s⁆ = ∑' t, ⁅= (x, t) | simulate so oa s⁆ :=
begin
  rw [prob_output.def, eval_dist_simulate', pmf.map_apply],
  refine (tsum_prod_eq_tsum_snd x $ λ s x' hx', _).trans (tsum_congr (λ s', _)),
  { simp only [ne.symm hx', if_false] },
  { simp only [prob_output.def, eq_self_iff_true, if_true] }
end

lemma prob_event_simulate' : ⁅e | simulate' so oa s⁆ = ⁅prod.fst ⁻¹' e | simulate so oa s⁆ :=
by rw [simulate', prob_event_map]

lemma prob_output_simulate'_eq_prob_event :
  ⁅= x | simulate' so oa s⁆ = ⁅prod.fst ⁻¹' {x} | simulate so oa s⁆ :=
by rw [← prob_event_singleton_eq_prob_output, prob_event_simulate']


end simulate'

end oracle_comp