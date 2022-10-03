import computational_monads.distribution_semantics.prob_event

/-!
# Oracle Simulation Semantics

Defines the notion of simulating a computation by defining the outputs of oracle query.
A method of simulation is given by `sim_oracle`, which contains an internal state
  as well as a function to return a value and update the state given a query to the oracle.

It also contains a `default_state`, specifying the value to use for the default oracle state.
For example a logging query would use an empty log as the default state.

We define `simulate'` to be simulation followed by discarding the state.
This is useful for things like a random oracle, where the final result isn't relevant in general.

-/

open_locale nnreal ennreal

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
example : sim_oracle oracle_spec.coin_oracle oracle_spec.coin_oracle ℕ :=
{ default_state := 0,
  o := λ i ⟨t, n⟩, return (if even n then tt else ff, n + 1) }

/-- View a simulation oracle as a function corresponding to the internal oracle `o` -/
instance has_coe_to_fun : has_coe_to_fun (sim_oracle spec spec' S)
  (λ so, Π (i : spec.ι), spec.domain i × S → oracle_comp spec' (spec.range i × S)) :=
{ coe := λ so, so.o }

lemma has_coe_to_fun_def (so : sim_oracle spec spec' S) (i : spec.ι)
  (x : spec.domain i × S) : so i x = so.o i x := rfl

def inhabited_state (so : sim_oracle spec spec' S) : inhabited S := ⟨so.default_state⟩

instance inhabited [inhabited S] : inhabited (sim_oracle spec spec' S) :=
⟨{default_state := default, o := λ _ _, return default}⟩

end sim_oracle

namespace oracle_comp

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa oa' : oracle_comp spec α)
  (ob ob' : α → oracle_comp spec β) (s : S) (f : α → β)

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
@[inline, reducible]
def default_simulate (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' (α × S) := simulate so oa so.default_state

@[simp] -- TODO: seems like simp tags here get applied more eagerly, prob bad
-- Problem being that simp starts with inner most terms
-- Could also try using simp attributes to decide which simp lemmas to use
-- i.e. we should have a `unfold_simulate_simps`
-- On the other hand maybe this just indicates the lower level simp lemmas aren't goode enough
lemma simulate_return : simulate so (return a) s = return (a, s) := rfl

lemma simulate_pure' : simulate so (pure' α a) s = return (a, s) := rfl

lemma simulate_pure : simulate so (pure a) s = return (a, s) := rfl

@[simp]
lemma simulate_bind : simulate so (oa >>= ob) s
  = simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma simulate_bind' : simulate so (bind' α β oa ob) s
  = simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp]
lemma simulate_query : simulate so (query i t) s = so i (t, s) := rfl

@[simp]
lemma simulate_map : simulate so (f <$> oa) s = prod.map f id <$> simulate so oa s := rfl

section support

lemma support_simulate_return : (simulate so (return a) s).support = {(a, s)} := rfl

lemma support_simulate_pure' : (simulate so (pure' α a) s).support = {(a, s)} := rfl

lemma support_simulate_pure : (simulate so (pure a) s).support = {(a, s)} := rfl

lemma support_simulate_bind : (simulate so (oa >>= ob) s).support
  = ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_simulate_bind' : (simulate so (bind' α β oa ob) s).support
  = ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_simulate_query : (simulate so (query i t) s).support = (so i (t, s)).support := rfl

lemma support_simulate_map : (simulate so (f <$> oa) s).support =
  prod.map f id '' (simulate so oa s).support := by rw [simulate_map, support_map]

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

lemma eval_dist_simulate_return : ⦃simulate so (return a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate_pure' : ⦃simulate so (pure' α a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate_pure : ⦃simulate so (pure a) s⦄ = pmf.pure (a, s) := rfl

@[simp]
lemma eval_dist_simulate_bind : ⦃simulate so (oa >>= ob) s⦄ =
  (⦃simulate so oa s⦄).bind (λ x, ⦃simulate so (ob x.1) x.2⦄) :=
(congr_arg _ $ simulate_bind so oa ob s).trans (eval_dist_bind _ _)

lemma eval_dist_simulate_bind' : ⦃simulate so (bind' α β oa ob) s⦄ =
  (⦃simulate so oa s⦄).bind (λ x, ⦃simulate so (ob x.1) x.2⦄) :=
eval_dist_simulate_bind so oa ob s

lemma eval_dist_simulate_query : ⦃simulate so (query i t) s⦄ = ⦃so i (t, s)⦄ := rfl

lemma eval_dist_simulate_map : ⦃simulate so (f <$> oa) s⦄ =
  ⦃simulate so oa s⦄.map (prod.map f id) := by rw [simulate_map, eval_dist_map]

lemma eval_dist_simulate_bind_apply_eq_tsum_tsum (x : β × S) : ⦃simulate so (oa >>= ob) s⦄ x =
  ∑' (a : α) (s' : S), ⦃simulate so oa s⦄ (a, s') * ⦃simulate so (ob a) s'⦄ x :=
begin
  rw [eval_dist_simulate_bind, pmf.bind_apply],
  refine tsum_prod' (nnreal.summable_of_le (λ x, mul_le_of_le_of_le_one le_rfl
    (pmf.apply_le_one _ _)) (pmf.summable_coe ⦃simulate so oa s⦄)) (λ a, _),
  have : summable (λ s', ⦃simulate so oa s⦄ (a, s')),
  from nnreal.summable_comp_injective (pmf.summable_coe ⦃simulate so oa s⦄)
    (λ s s' hs, (prod.eq_iff_fst_eq_snd_eq.1 hs).2),    refine nnreal.summable_of_le _ this,
  exact λ s, mul_le_of_le_of_le_one le_rfl (pmf.apply_le_one _ _)
end

end eval_dist

section equiv

lemma simulate_return_equiv : simulate so (return a) s ≃ₚ
  (return (a, s) : oracle_comp spec' (α × S)) := rfl

lemma simulate_pure'_equiv : simulate so (pure' α a) s ≃ₚ
  (return (a, s) : oracle_comp spec' (α × S)) := rfl

lemma simulate_pure_equiv : simulate so (pure a) s ≃ₚ
  (pure (a, s) : oracle_comp spec' (α × S)) := rfl

lemma simulate_bind_equiv : simulate so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma simulate_bind'_equiv : simulate so (bind' α β oa ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma simulate_query_equiv : simulate so (query i t) s ≃ₚ so i (t, s) := rfl

lemma simulate_map_equiv : simulate so (f <$> oa) s ≃ₚ prod.map f id <$> simulate so oa s :=
by simp only [eval_dist_simulate_map, eval_dist_map]

end equiv

section prob_event


end prob_event

end distribution_semantics

end simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
def simulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S) :
  oracle_comp spec' α := prod.fst <$> oa.simulate so s

/-- Convenience definition to use the default state as the initial state for `simulate'`.
Marked to be reduced and inlined, so the definition is essentially just notation. -/
@[inline, reducible]
def default_simulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' α := oa.simulate' so so.default_state

lemma simulate'_def : simulate' so oa s = prod.fst <$> oa.simulate so s := rfl

-- TODO: these especially might be weird with simp lemmas? again maybe a lower level problem though
@[simp]
lemma simulate'_return : simulate' so (return a) s = prod.fst <$> (return (a, s)) := rfl

lemma simulate'_pure' : simulate' so (pure' α a) s = prod.fst <$> (return (a, s)) := rfl

lemma simulate'_pure : simulate' so (pure a) s = prod.fst <$> (return (a, s)) := rfl

@[simp]
lemma simulate'_bind : simulate' so (oa >>= ob) s =
  prod.fst <$> (simulate so oa s >>= λ x, simulate so (ob x.1) x.2) := rfl

lemma simulate'_bind' : simulate' so (bind' α β oa ob) s =
  prod.fst <$> (simulate so oa s >>= λ x, simulate so (ob x.1) x.2) := rfl

@[simp]
lemma simulate'_query : simulate' so (query i t) s = prod.fst <$> so i (t, s) := rfl

@[simp]
lemma simulate'_map : simulate' so (f <$> oa) s =
  prod.fst <$> (prod.map f id <$> simulate so oa s) := rfl

section support

@[simp]
lemma support_simulate' : (simulate' so oa s).support =
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

@[simp]
lemma support_simulate'_bind : (simulate' so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
by simp [set.image_Union]

lemma support_simulate'_bind' : (simulate' so (bind' α β oa ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
support_simulate'_bind so oa ob s

lemma support_simulate'_query : (simulate' so (query i t) s).support =
  prod.fst '' (so i (t, s)).support := by simp only [simulate'_query, support_map]

@[simp] -- example of why more specific simp lemmas are maybe better
lemma support_simulate'_map : (simulate' so (f <$> oa) s).support =
  f '' (simulate' so oa s).support :=
by simp only [simulate', support_map, support_simulate_map, set.image_image, prod.map_fst]

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

@[simp]
lemma eval_dist_simulate' : ⦃simulate' so oa s⦄ = ⦃simulate so oa s⦄.map prod.fst :=
eval_dist_map _ prod.fst

/-- Express the probability of `simulate'` returning a specific value
as the sum over all possible output states of the probability of `simulate` return it -/
lemma eval_dist_simulate'_apply :
  ⦃simulate' so oa s⦄ a = ∑' (s' : S), ⦃simulate so oa s⦄ (a, s') :=
begin
  rw [eval_dist_simulate', pmf.map_apply],
  refine (tsum_prod_eq_tsum_snd a $ λ a' ha' s, _).trans (tsum_congr (λ s', _)),
  { simp only [ne.symm ha', if_false] },
  { simp only [eq_self_iff_true, if_true] }
end

lemma eval_dist_simulate'_return : ⦃simulate' so (return a) s⦄ = pmf.pure a :=
by simp only [simulate'_return, map_return_equiv, eval_dist_return]

lemma eval_dist_simulate'_pure' : ⦃simulate' so (pure' α a) s⦄ = pmf.pure a :=
eval_dist_simulate'_return so a s

lemma eval_dist_simulate'_pure : ⦃simulate' so (pure a) s⦄ = pmf.pure a :=
eval_dist_simulate'_return so a s

lemma eval_dist_simulate'_bind : ⦃simulate' so (oa >>= ob) s⦄ =
  ⦃simulate so oa s⦄.bind (λ x, ⦃simulate' so (ob x.1) x.2⦄) :=
by simp only [simulate'_bind, map_bind_equiv, eval_dist_bind, eval_dist_map,
  eval_dist_simulate', eq_self_iff_true, pmf.map_bind]

lemma eval_dist_simulate'_bind_apply (b : β) : ⦃simulate' so (oa >>= ob) s⦄ b
  = ∑' (a : α) (s' : S), ⦃simulate so oa s⦄ (a, s') * ⦃simulate' so (ob a) s'⦄ b :=
calc ⦃simulate' so (oa >>= ob) s⦄ b
  = ∑' (t : S) (a : α) (s' : S), ⦃simulate so oa s⦄ (a, s') * ⦃simulate so (ob a) s'⦄ (b, t) :
    by simp_rw [eval_dist_simulate'_apply, eval_dist_simulate_bind_apply_eq_tsum_tsum]
  ... = ∑' (a : α) (t s' : S), ⦃simulate so oa s⦄ (a, s') * ⦃simulate so (ob a) s'⦄ (b, t) :
    begin
      sorry
    end
  ... = ∑' (a : α) (s' t : S), ⦃simulate so oa s⦄ (a, s') * ⦃simulate so (ob a) s'⦄ (b, t) :
    begin
      refine tsum_congr (λ a, _),
      sorry
    end
  ... = ∑' (a : α) (s' : S), ⦃simulate so oa s⦄ (a, s') * ⦃simulate' so (ob a) s'⦄ b :
    by simp_rw [eval_dist_simulate'_apply, ← nnreal.tsum_mul_left]

lemma eval_dist_simulate'_bind' : ⦃simulate' so (bind' α β oa ob) s⦄ =
  ⦃simulate so oa s⦄.bind (λ x, ⦃simulate' so (ob x.1) x.2⦄) := eval_dist_simulate'_bind _ _ _ s

lemma eval_dist_simulate'_query : ⦃simulate' so (query i t) s⦄ = ⦃so i (t, s)⦄.map prod.fst :=
by simp only [simulate'_query, eval_dist_map]

@[simp]
lemma eval_dist_simulate'_map : ⦃simulate' so (f <$> oa) s⦄ = ⦃simulate' so oa s⦄.map f :=
by simp_rw [eval_dist_simulate', eval_dist_simulate_map, pmf.map_comp, prod.map_fst']

end eval_dist

section equiv

lemma simulate'_equiv_fst_map_simulate :
  simulate' so oa s ≃ₚ prod.fst <$> simulate so oa s := rfl

lemma simulate'_return_equiv : simulate' so (return a) s ≃ₚ
  (return a : oracle_comp spec' α) := by simp only [simulate'_return, map_return_equiv]

lemma simulate'_pure'_equiv : simulate' so (pure' α a) s ≃ₚ
  (return a : oracle_comp spec' α) := simulate'_return_equiv so a s

lemma simulate'_pure_equiv : simulate' so (pure a) s ≃ₚ
  (return a : oracle_comp spec' α) := simulate'_return_equiv so a s

lemma simulate'_bind_equiv : simulate' so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 :=
by simp only [simulate'_equiv_fst_map_simulate, simulate_bind, map_bind_equiv,
  eval_dist_bind, simulate'_equiv_fst_map_simulate]

lemma simulate'_bind'_equiv : simulate' so (bind' α β oa ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 :=
simulate'_bind_equiv so oa ob s

lemma simulate'_query_equiv : simulate' so (query i t) s ≃ₚ
  prod.fst <$> (so i (t, s)) := rfl

lemma simulate'_map_equiv (f : α → β) : simulate' so (f <$> oa) s ≃ₚ f <$> simulate' so oa s :=
by simp only [simulate_map_equiv, eval_dist_map, pmf.map_comp,
  prod.map_fst', simulate'_equiv_fst_map_simulate]

end equiv

section prob_event


end prob_event

end distribution_semantics

end simulate'


end oracle_comp