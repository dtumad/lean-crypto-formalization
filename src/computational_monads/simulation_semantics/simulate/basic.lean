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

open_locale big_operators ennreal
open oracle_spec

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulate` gives a method for applying a simulation oracle to a specific computation. -/
def sim_oracle (spec spec' : oracle_spec) (S : Type) :=
Π (i : spec.ι), spec.domain i × S → oracle_comp spec' (spec.range i × S)

/-- Example of an oracle maintaining in internal incrementing value,
and returning a fake coin flip that alternates between heads and tails. -/
example : sim_oracle oracle_spec.coin_spec oracle_spec.coin_spec ℕ :=
λ i ⟨t, n⟩, return (if even n then tt else ff, n + 1)

instance sim_oracle.inhabited [inhabited S] : inhabited (sim_oracle spec spec' S) :=
⟨λ _ _, oracle_comp.pure' _ default⟩

instance sim_oracle.decidable_eq [fintype spec.ι] [∀ i, fintype (spec.domain i)] [fintype S]
  [decidable_eq S] : decidable_eq (sim_oracle spec spec' S) :=
begin
  intros so so',
  have : so = so' ↔ ∀ (z : Σ i : spec.ι, spec.domain i × S), so z.1 z.2 = so' z.1 z.2,
  by simp_rw [function.funext_iff, sigma.forall],
  rw [this],
  have : ∀ i z, decidable (so i z = so' i z) := λ i z, oracle_comp.decidable_eq (so i z) (so' i z),
  exact @fintype.decidable_forall_fintype _ _ (λ z : Σ i, spec.domain i × S, this z.1 z.2) _,
end

namespace oracle_comp

variables (so : sim_oracle spec spec' S)

section simulate

/-- Simulate a computation by replacing queries to the oracle with some new computation.
Additionally returns the final internal state after the simulation. -/
def simulate (so : sim_oracle spec spec' S) : Π {α : Type},
  oracle_comp spec α → S → oracle_comp spec' (α × S)
| _ (pure' α a) state := return ⟨a, state⟩
| _ (query_bind' i t α oa) state := do {x ← so i (t, state), simulate (oa x.1) x.2}

@[simp] lemma simulate_return (a : α) (s : S) : simulate so (return a) s = return (a, s) := rfl

@[simp] lemma simulate_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s : S) :
  simulate so (oa >>= ob) s = simulate so oa s >>= λ x, simulate so (ob x.1) x.2 :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { simp [simulate_return] },
  { simp_rw [bind_assoc, ← query_bind'_eq_query_bind, simulate, hoa, ← bind_assoc] }
end

@[simp] lemma simulate_query (i : spec.ι) (t : spec.domain i) (s : S) :
  simulate so (query i t) s = so i (t, s) :=
by simp_rw [query_def, simulate, prod.mk.eta, bind_pure]

@[simp] lemma simulate_map (oa : oracle_comp spec α) (f : α → β) (s : S) :
  simulate so (f <$> oa) s = prod.map f id <$> simulate so oa s :=
by simpa only [map_eq_bind_pure_comp, simulate_bind]

end simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
def simulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S) :
  oracle_comp spec' α := prod.fst <$> oa.simulate so s

lemma simulate'.def (oa : oracle_comp spec α) (s : S) :
  simulate' so oa s = prod.fst <$> oa.simulate so s := rfl

@[simp] lemma simulate'_return (a : α) (s : S) : simulate' so (return a) s = return a := rfl

@[simp] lemma simulate'_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s : S) :
  simulate' so (oa >>= ob) s = simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 :=
by simp_rw [simulate'.def, simulate_bind, map_bind]

@[simp] lemma simulate'_query (i : spec.ι) (t : spec.domain i) (s : S) :
  simulate' so (query i t) s = prod.fst <$> so i (t, s) :=
congr_arg ((<$>) prod.fst) (simulate_query so i t s)

@[simp] lemma simulate'_map (oa : oracle_comp spec α) (f : α → β) (s : S) :
  simulate' so (f <$> oa) s = f <$> simulate' so oa s :=
by simpa only [simulate'.def, simulate_map, map_map_eq_map_comp]

section eval_dist

variables (oa : oracle_comp spec α) (s : S)

lemma simulate'_dist_equiv : simulate' so oa s ≃ₚ prod.fst <$> simulate so oa s := dist_equiv.rfl

@[simp] lemma support_simulate' :
  (simulate' so oa s).support = prod.fst '' (simulate so oa s).support :=
by simp only [simulate', support_map]

lemma mem_support_simulate'_iff_exists_state (x : α) :
  x ∈ (simulate' so oa s).support ↔ ∃ (s' : S), (x, s') ∈ (simulate so oa s).support :=
by simp [support_simulate', set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right]

@[simp] lemma fin_support_simulate' [decidable_eq α] [decidable_eq S] :
  (simulate' so oa s).fin_support = (simulate so oa s).fin_support.image prod.fst :=
by simp only [simulate', fin_support_map]

lemma mem_fin_support_simulate'_iff_exists_state (x : α) [decidable_eq α] [decidable_eq S] :
  x ∈ (simulate' so oa s).fin_support ↔ ∃ (s' : S), (x, s') ∈ (simulate so oa s).fin_support :=
by simp_rw [mem_fin_support_iff_mem_support, mem_support_simulate'_iff_exists_state] 

@[simp] lemma eval_dist_simulate' : ⁅simulate' so oa s⁆ = ⁅simulate so oa s⁆.map prod.fst :=
eval_dist_map _ prod.fst

lemma prob_output_simulate'_eq_tsum (x : α) :
  ⁅= x | simulate' so oa s⁆ = ∑' s' : S, ⁅= (x, s') | simulate so oa s⁆ :=
begin
  rw [prob_output.def, eval_dist_simulate', pmf.map_apply],
  refine (tsum_prod_eq_tsum_snd x $ λ s x' hx', _).trans (tsum_congr (λ s', _)),
  { simp only [ne.symm hx', if_false] },
  { simp only [prob_output.def, eq_self_iff_true, if_true] }
end

lemma prob_output_simulate'_eq_sum [fintype S] (x : α) :
  ⁅= x | simulate' so oa s⁆ = ∑ s' : S, ⁅= (x, s') | simulate so oa s⁆ :=
trans (prob_output_simulate'_eq_tsum so oa s x)
  (tsum_eq_sum (λ s' hs', (hs' (finset.mem_univ s')).elim)) 

@[simp] lemma prob_event_simulate' (p : α → Prop) :
  ⁅p | simulate' so oa s⁆ = ⁅p ∘ prod.fst | simulate so oa s⁆ := prob_event_map _ _ p

lemma prob_output_simulate'_eq_prob_event_simulate (x : α) :
  ⁅= x | simulate' so oa s⁆ = ⁅λ z, x = z.1 | simulate so oa s⁆ :=
by rw [← prob_event_eq_eq_prob_output, prob_event_simulate', function.comp]

end eval_dist

end simulate'

lemma simulate_eq_map_simulate'_of_subsingleton [subsingleton S] (oa : oracle_comp spec α)
  (s s' : S) : simulate so oa s = (λ x, (x, s')) <$> simulate' so oa s :=
begin
  rw [simulate', map_map_eq_map_comp],
  refine trans (symm (id_map' _)) (congr_fun (congr_arg _ (funext (λ z, _))) _),
  simp [prod.eq_iff_fst_eq_snd_eq],
end

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

/-- Compatibility of a mapping between the states of two simulation oracles. -/
lemma prod_map_id_simulate_eq_simulate
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec' S')
  (f : S → S') (h : ∀ i t s, prod.map id f <$> so i (t, s) = so' i (t, f s))
  (oa : oracle_comp spec α) (s : S) :
  prod.map id f <$> simulate so oa s = simulate so' oa (f s) :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { simp only [simulate_return, map_pure, prod.map_mk, id.def] },
  { simp_rw [simulate_bind, simulate_query, map_bind, ← h, oracle_comp.bind_map, hoa,
      function.comp, prod_map, id.def] }
end

section support_subset

variables (oa : oracle_comp spec α) (s : S)

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