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

We intentionally avoid marking lemmas like `simulate_return` as `@[simp]`, as some proofs
are expressed more easily when things haven't been reduced like this.
Instead we mark things like `support_simulate_return`.
TODO: we should evaluate if this approach is actually always better.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation.
`default_state` can be provided as a standard initial state for simulation (`dsimulate`). -/
structure sim_oracle (spec spec' : oracle_spec) (S : Type) :=
(default_state : S)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

namespace sim_oracle

/-- Example of an oracle maintaining in internal incrementing value,
and returning a fake coin flip that alternates between heads and tails. -/
noncomputable example : sim_oracle oracle_spec.coin_spec oracle_spec.coin_spec ℕ :=
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
⟨{default_state := default, o := λ _ _, oracle_comp.pure' _ default}⟩

end sim_oracle

namespace oracle_comp

open_locale big_operators ennreal
open oracle_spec

variables (so : sim_oracle spec spec' S) (a : α) (i : spec.ι) (t : spec.domain i)
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (f : α → β) (s : S) (x : α) (e : set α)

section simulate

/-- Simulate a computation by replacing queries to the oracle with some new computation.
Additionally returns the final internal state after the simulation. -/
noncomputable def simulate (so : sim_oracle spec spec' S) : Π {α : Type},
  oracle_comp spec α → S → oracle_comp spec' (α × S)
| _ (pure' α a) state := return ⟨a, state⟩
| _ (query_bind' i t α oa) state := do {x ← so i (t, state), simulate (oa x.1) x.2}

/-- Convenience definition to use the default state as the initial state for `simulate`.
Marked to be reduced and inlined, so the definition is essentially just notational. -/
@[inline, reducible, simp]
noncomputable def dsimulate (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' (α × S) := simulate so oa so.default_state

lemma simulate_return : simulate so (return a) s = return (a, s) := rfl

lemma simulate_bind : simulate so (oa >>= ob) s =
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { simp [simulate_return] },
  { simp_rw [bind_assoc, ← query_bind'_eq_query_bind, simulate, hoa, ← bind_assoc] }
end

lemma simulate_query : simulate so (query i t) s = so i (t, s) :=
by simp_rw [query_def, simulate, prod.mk.eta, bind_pure]

lemma simulate_map : simulate so (f <$> oa) s = prod.map f id <$> simulate so oa s :=
by simpa only [map_eq_bind_pure_comp, simulate_bind]

end simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
noncomputable def simulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S) :
  oracle_comp spec' α := prod.fst <$> oa.simulate so s

/-- Convenience definition to use the default state as the initial state for `simulate'`.
Marked to be reduced and inlined, so the definition is essentially just notation. -/
@[inline, reducible, simp]
noncomputable def dsimulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' α := oa.simulate' so so.default_state

lemma simulate'_def : simulate' so oa s = prod.fst <$> oa.simulate so s := rfl

-- TODO: these should have a special simp category, to not be eagerly applied
lemma simulate'_return : simulate' so (return a) s = prod.fst <$> (return (a, s)) := rfl

lemma simulate'_bind : simulate' so (oa >>= ob) s =
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 :=
by simp [simulate'_def, simulate_bind, map_bind]

lemma simulate'_query : simulate' so (query i t) s = prod.fst <$> so i (t, s) :=
by rw [simulate'_def, simulate_query]

lemma simulate'_map : simulate' so (f <$> oa) s = f <$> simulate' so oa s :=
by simpa [simulate'_def, simulate_map]

@[simp] lemma support_simulate' :
  (simulate' so oa s).support = prod.fst '' (simulate so oa s).support :=
by simp only [simulate', support_map]

@[simp] lemma fin_support_simulate' [decidable_eq α] [decidable_eq S] :
  (simulate' so oa s).fin_support = (simulate so oa s).fin_support.image prod.fst :=
by simp only [simulate', fin_support_map]

/-- An element is a possible output of `simulate'` if there is some simulation state
such that the element and state are together a possible output of `simulate`. -/
lemma mem_support_simulate'_iff_exists_state (x : α) :
  x ∈ (simulate' so oa s).support ↔ ∃ (s' : S), (x, s') ∈ (simulate so oa s).support :=
by simp only [support_simulate', set.mem_image, prod.exists,
  exists_and_distrib_right, exists_eq_right]

@[simp] lemma eval_dist_simulate' : ⁅simulate' so oa s⁆ = ⁅simulate so oa s⁆.map prod.fst :=
eval_dist_map _ prod.fst

lemma simulate'_dist_equiv : simulate' so oa s ≃ₚ prod.fst <$> simulate so oa s := refl _

/-- Express the probability of `simulate'` returning a specific value
as the sum over all possible output states of the probability of `simulate` return it -/
lemma prob_output_simulate' : ⁅= x | simulate' so oa s⁆ = ∑' t, ⁅= (x, t) | simulate so oa s⁆ :=
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

/-- If some invariant `P` on the state of a simulation oracle is preserved by any query
where the input state satisfies `P`, and some initial state also satisfies `P`,
then any result of the simulation will have a final state satisfying `P`. -/
lemma state_invariant_of_preserved (so : sim_oracle spec spec' S) (P : S → Prop)
  (hso : ∀ i t s, ∀ x ∈ (so i (t, s)).support, P s → P (prod.snd x)) (s : S) (hs : P s)
  (oa : oracle_comp spec α) (x : α × S) (hx : x ∈ (simulate so oa s).support) : P x.2 :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { exact (symm hx) ▸ hs },
  { rw [simulate_bind, simulate_query] at hx,
    obtain ⟨x', h, hx⟩ := (mem_support_bind_iff _ _ _).1 hx,
    exact hoa x'.1 x x'.2 (hso i t s x' h hs) hx }
end

section support_subset

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support.
In particular the support of a simulation lies in the pullback of the original support. -/
lemma support_simulate_subset_preimage_support :
  (simulate so oa s).support ⊆ prod.fst ⁻¹' oa.support :=
begin
  rw [set.preimage],
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp [simulate_return] },
  { simp only [simulate_bind, support_bind, set.Union_subset_iff,
      support_bind, set.mem_Union, exists_prop],
    refine λ x hx b hb, ⟨x.1, hoa s hx, hob x.1 x.2 hb⟩ },
  { simp [support_query] }
end

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support. In particular
the first output of a simulation has support at most that of the original computation -/
lemma support_simulate'_subset_support : (simulate' so oa s).support ⊆ oa.support :=
begin
  refine (support_simulate' so oa s).symm ▸ λ x hx, _,
  obtain ⟨y, hy, rfl⟩ := (set.mem_image prod.fst _ _).1 hx,
  exact support_simulate_subset_preimage_support so oa s hy,
end

lemma mem_support_of_mem_support_simulate (x : α × S) (hx : x ∈ (simulate so oa s).support) :
  x.1 ∈ oa.support := by simpa using (support_simulate_subset_preimage_support so oa s hx)

lemma mem_support_of_mem_support_simulate' (x : α)
  (hx : x ∈ (simulate' so oa s).support) : x ∈ oa.support :=
support_simulate'_subset_support so oa s hx

end support_subset

end oracle_comp