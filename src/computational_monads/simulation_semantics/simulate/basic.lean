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

-- TODO!!: organize this folder more like the `distribution_semantics` one
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
  e.g. using uniform random selection to simulate a hash oracle

  `default_state` can be provided as a standard initial state for simulation.
  Used when calling `default_simulate` or `default_simulate'` -/
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

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa oa' : oracle_comp spec α)
  (ob ob' : α → oracle_comp spec β) (oc : β → oracle_comp spec γ) (s : S) (f : α → β)

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

lemma simulate_pure' : simulate so (pure' α a) s = return (a, s) := rfl

lemma simulate_pure : simulate so (pure a) s = return (a, s) := rfl

@[simp] lemma simulate_bind : simulate so (oa >>= ob) s =
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma simulate_bind' : simulate so (bind' α β oa ob) s =
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp] lemma simulate_query : simulate so (query i t) s = so i (t, s) := rfl

@[simp] lemma simulate_map : simulate so (f <$> oa) s = prod.map f id <$> simulate so oa s := rfl

section support

lemma support_simulate_return : (simulate so (return a) s).support = {(a, s)} := rfl

lemma support_simulate_pure' : (simulate so (pure' α a) s).support = {(a, s)} := rfl

lemma support_simulate_pure : (simulate so (pure a) s).support = {(a, s)} := rfl

lemma support_simulate_bind : (simulate so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma mem_support_simulate_bind_iff (x : β × S) : x ∈ (simulate so (oa >>= ob) s).support ↔
  ∃ (a : α) (s' : S), (a, s') ∈ (simulate so oa s).support ∧ x ∈ (simulate so (ob a) s').support :=
by simp_rw [support_simulate_bind, set.mem_Union, prod.exists, exists_prop]

lemma support_simulate_bind' : (simulate so (bind' α β oa ob) s).support
  = ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_simulate_query : (simulate so (query i t) s).support = (so i (t, s)).support := rfl

lemma support_simulate_map : (simulate so (f <$> oa) s).support =
  prod.map f id '' (simulate so oa s).support := by rw [simulate_map, support_map]

end support

section fin_support



end fin_support

section eval_dist

lemma eval_dist_simulate_return : ⁅simulate so (return a) s⁆ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate_pure' : ⁅simulate so (pure' α a) s⁆ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate_pure : ⁅simulate so (pure a) s⁆ = pmf.pure (a, s) := rfl

@[simp] lemma eval_dist_simulate_bind : ⁅simulate so (oa >>= ob) s⁆ =
  (⁅simulate so oa s⁆).bind (λ x, ⁅simulate so (ob x.1) x.2⁆) :=
(congr_arg _ $ simulate_bind so oa ob s).trans (eval_dist_bind _ _)

lemma eval_dist_simulate_bind' : ⁅simulate so (bind' α β oa ob) s⁆ =
  (⁅simulate so oa s⁆).bind (λ x, ⁅simulate so (ob x.1) x.2⁆) :=
eval_dist_simulate_bind so oa ob s

lemma eval_dist_simulate_query : ⁅simulate so (query i t) s⁆ = ⁅so i (t, s)⁆ := rfl

lemma eval_dist_simulate_map : ⁅simulate so (f <$> oa) s⁆ =
  ⁅simulate so oa s⁆.map (prod.map f id) := by rw [simulate_map, eval_dist_map]

/-- Write the `eval_dist` of a simulation as a double summation over the possible
intermediate outputs and states of the computation. -/
lemma prob_output_simulate_bind_eq_tsum_tsum (x : β × S) : ⁅= x | simulate so (oa >>= ob) s⁆ =
  ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= x | simulate so (ob a) s'⁆ :=
by rw [simulate_bind, eval_dist_prod_bind]

lemma prob_output_simulate_bind_eq_sum_sum [fintype α] [fintype S] (x : β × S) :
  ⁅= x | simulate so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅= x | simulate so (ob a) s'⁆ :=
by simp only [simulate_bind, prob_output_bind_eq_sum, ← @finset.sum_product ℝ≥0∞ S α _
  finset.univ finset.univ (λ y, ⁅= (y.1, y.2) | simulate so oa s⁆ * ⁅= x | simulate so (ob y.1) y.2⁆),
  finset.univ_product_univ, prod.mk.eta]

end eval_dist

section prob_event

lemma prob_event_simulate_return (e : set (α × S)) :
  ⁅e | simulate so (return a) s⁆ = e.indicator (λ _, 1) (a, s) :=
prob_event_return_eq_indicator _ (a, s) e

lemma prob_event_simulate_bind_eq_tsum_tsum (e : set (β × S)) : ⁅e | simulate so (oa >>= ob) s⁆ =
  ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate so (ob a) s'⁆ :=
by simp_rw [simulate_bind, prob_event_bind_eq_tsum, ← ennreal.tsum_prod, prod.mk.eta]

lemma prob_event_simulate_bind_eq_sum_sum [fintype α] [fintype S] (e : set (β × S)) :
  ⁅e | simulate so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate so (ob a) s'⁆ :=
by simp only [simulate_bind, prob_event_bind_eq_sum, ← @finset.sum_product ℝ≥0∞ S α _ finset.univ
  finset.univ (λ x, ⁅= (x.1, x.2) | simulate so oa s⁆ * ⁅e | simulate so (ob x.1) x.2⁆),
  finset.univ_product_univ, prod.mk.eta]

lemma prob_event_simulate_query (e : set (spec.range i × S)) :
  ⁅e | simulate so (query i t) s⁆ = ⁅e | so i (t, s)⁆ := rfl

lemma prob_event_simulate_map (e : set (β × S)) :
  ⁅e | simulate so (f <$> oa) s⁆ = ⁅prod.map f id ⁻¹' e | simulate so oa s⁆ :=
by rw [simulate_map, prob_event_map]

end prob_event

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

section support

@[simp] lemma support_simulate' : (simulate' so oa s).support =
  prod.fst '' (simulate so oa s).support := by simp only [simulate', support_map]

lemma mem_support_simulate'_iff_exists_state (a : α) :
  a ∈ (simulate' so oa s).support ↔ ∃ (s' : S), (a, s') ∈ (simulate so oa s).support :=
by simp only [support_simulate', set.mem_image, prod.exists,
  exists_and_distrib_right, exists_eq_right]

lemma support_simulate'_return (a : α) : (simulate' so (return a) s).support = {a} :=
by simp only [simulate'_return, support_map, support_return, set.image_singleton]

lemma support_simulate'_pure' (a : α) : (simulate' so (pure' α a) s).support = {a} :=
support_simulate'_return so s a

lemma support_simulate'_pure (a : α) : (simulate' so (pure a) s).support = {a} :=
support_simulate'_return so s a

@[simp] lemma support_simulate'_bind : (simulate' so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
by simp [set.image_Union]

lemma support_simulate'_bind' : (simulate' so (bind' α β oa ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
support_simulate'_bind so oa ob s

lemma support_simulate'_query : (simulate' so (query i t) s).support =
  prod.fst '' (so i (t, s)).support := by simp only [simulate'_query, support_map]

@[simp] lemma support_simulate'_map : (simulate' so (f <$> oa) s).support =
  f '' (simulate' so oa s).support :=
by simp only [simulate', support_map, support_simulate_map, set.image_image, prod.map_fst]

end support

section eval_dist

@[simp] lemma eval_dist_simulate' : ⁅simulate' so oa s⁆ = ⁅simulate so oa s⁆.map prod.fst :=
eval_dist_map _ prod.fst

/-- Express the probability of `simulate'` returning a specific value
as the sum over all possible output states of the probability of `simulate` return it -/
lemma prob_output_simulate' : ⁅= a | simulate' so oa s⁆ = ∑' s', ⁅= (a, s') | simulate so oa s⁆ :=
begin
  rw [prob_output.def, eval_dist_simulate', pmf.map_apply],
  refine (tsum_prod_eq_tsum_snd a $ λ s a' ha', _).trans (tsum_congr (λ s', _)),
  { simp only [ne.symm ha', if_false] },
  { simp only [prob_output.def, eq_self_iff_true, if_true] }
end

lemma eval_dist_simulate'_return : ⁅simulate' so (return a) s⁆ = pmf.pure a :=
by simp only [simulate'_return, eval_dist_map, eval_dist_return, pmf.map_pure]

lemma eval_dist_simulate'_bind : ⁅simulate' so (oa >>= ob) s⁆ =
  ⁅simulate so oa s⁆.bind (λ x, ⁅simulate' so (ob x.1) x.2⁆) :=
by simp only [simulate'_bind, eval_dist_map_bind, eval_dist_bind, eval_dist_map,
  eval_dist_simulate', eq_self_iff_true, pmf.map_bind]

-- lemma prob_output_simulate'_bind (b : β) : ⁅= b | simulate' so (oa >>= ob) s⁆
--   = ∑' (a : α) (s' : S), ⁅= (a, s') | simulate so oa s⁆ * ⁅= b | simulate' so (ob a) s'⁆ :=
-- begin
--   simp [simulate'_bind, prob_output_map_eq_tsum_indicator, ennreal.tsum_prod'],
-- end

lemma eval_dist_simulate'_query : ⁅simulate' so (query i t) s⁆ = ⁅so i (t, s)⁆.map prod.fst :=
by simp only [simulate'_query, eval_dist_map]

@[simp] lemma eval_dist_simulate'_map : ⁅simulate' so (f <$> oa) s⁆ = ⁅simulate' so oa s⁆.map f :=
by simp_rw [eval_dist_simulate', eval_dist_simulate_map, pmf.map_comp, prod.map_fst']

end eval_dist

section prob_event

lemma prob_event_simulate' (e : set α) :
  ⁅e | simulate' so oa s⁆ = ⁅prod.fst ⁻¹' e | simulate so oa s⁆ :=
by rw [simulate', prob_event_map]

lemma prob_event_simulate'_return_eq_indicator (e : set α) :
  ⁅e | simulate' so (return a) s⁆ = e.indicator (λ _, 1) a :=
begin
  rw [prob_event_simulate', prob_event_simulate_return],
  by_cases ha : a ∈ e,
  { have : (a, s) ∈ (prod.fst ⁻¹' e : set (α × S)) := ha,
    rw [set.indicator_of_mem ha, set.indicator_of_mem this] },
  { have : (a, s) ∉ (prod.fst ⁻¹' e : set (α × S)) := ha,
    rw [set.indicator_of_not_mem ha, set.indicator_of_not_mem this] }
end

lemma prob_event_simulate'_return_eq_ite (e : set α) [decidable_pred (∈ e)] :
  ⁅e | simulate' so (return a) s⁆ = ite (a ∈ e) 1 0 :=
by {rw [prob_event_simulate'_return_eq_indicator, set.indicator], congr}

lemma prob_event_simulate'_bind_eq_tsum_tsum (e : set β) : ⁅e | simulate' so (oa >>= ob) s⁆ =
  ∑' a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_event_simulate', prob_event_simulate_bind_eq_tsum_tsum]

lemma prob_event_simulate'_bind_eq_sum_sum [fintype α] [fintype S] (e : set β) :
  ⁅e | simulate' so (oa >>= ob) s⁆ =
    ∑ a s', ⁅= (a, s') | simulate so oa s⁆ * ⁅e | simulate' so (ob a) s'⁆ :=
by simp_rw [prob_event_simulate', prob_event_simulate_bind_eq_sum_sum]

lemma prob_event_simulate'_query (e : set (spec.range i)) :
  ⁅e | simulate' so (query i t) s⁆ = ⁅prod.fst ⁻¹' e | so i (t, s)⁆ :=
by rw [prob_event_simulate', prob_event_simulate_query]

lemma prob_event_simulate'_map (e : set β) :
  ⁅e | simulate' so (f <$> oa) s⁆ = ⁅(f ∘ prod.fst) ⁻¹' e | simulate so oa s⁆ :=
by simpa only [prob_event_simulate', prob_event_simulate_map, ← set.preimage_comp]

end prob_event

end simulate'

end oracle_comp