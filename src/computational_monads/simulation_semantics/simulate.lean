import computational_monads.distribution_semantics.prob_event

/-!
# Oracle Simulation Semantics

Defines the notion of simulating a computation by defining the outputs of oracle query.
A method of simulation is given by `simulation_oracle`, which contains an internal state
  as well as a function to return a value and update the state given a query to the oracle.

It also contains a `default_state`, specifying the value to use for the default oracle state.
For example a logging query would use an empty log as the default state.

We define `simulate'` to be simulation followed by discarding the state.
This is useful for things like a random oracle, where the final result isn't relevant in general.
-/

namespace oracle_comp

variables {α β γ : Type} {spec spec' spec'' : oracle_spec}

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle
  
  `default_state` can be provided as a standard initial state for simulation.
  Used when calling `default_simulate` or `default_simulate'` -/
structure simulation_oracle (spec spec' : oracle_spec) :=
(S : Type)
(default_state : S)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

/-- View a simulation oracle as a function corresponding to the internal oracle `o` -/
instance simulation_oracle.has_coe_to_fun : has_coe_to_fun (simulation_oracle spec spec')
  (λ so, Π (i : spec.ι), spec.domain i × so.S → oracle_comp spec' (spec.range i × so.S)) :=
{ coe := λ so, so.o }

lemma simulation_oracle.has_coe_to_fun_def (so : simulation_oracle spec spec') (i : spec.ι)
  (x : spec.domain i × so.S) : so i x = so.o i x := rfl

variables (so : simulation_oracle spec spec') (so' : simulation_oracle spec spec'')
variables (a : α) (i : spec.ι) (t : spec.domain i)
  (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) (s : so.S) (f : α → β)

section simulate

/-- Simulate an oracle comp to an oracle comp with a different spec.
  Requires providing a maximum recursion depth for the `repeat` constructor -/
def simulate {spec spec' : oracle_spec} (so : simulation_oracle spec spec') :
  Π {A : Type} (oa : oracle_comp spec A), so.S → oracle_comp spec' (A × so.S)
| _ (pure' A a) state := return ⟨a, state⟩
| _ (bind' A B oa ob) state := simulate oa state >>= λ x, simulate (ob x.1) x.2
| _ (query i t) state := so i (t, state)

@[simp]
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
lemma simulate_map : simulate so (f <$> oa) s = simulate so oa s >>= return ∘ prod.map f id := rfl

section support

lemma support_simulate_return : (simulate so (return a) s).support = {(a, s)} := rfl

lemma support_simulate_pure' : (simulate so (pure' α a) s).support = {(a, s)} := rfl

lemma support_simulate_pure : (simulate so (pure a) s).support = {(a, s)} := rfl

lemma support_simulate_bind : (simulate so (oa >>= ob) s).support
  = ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_simulate_bind' : (simulate so (bind' α β oa ob) s).support
  = ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_simulate_query : (simulate so (query i t) s).support = (so i (t, s)).support := rfl

@[simp]
lemma support_simulate_map : (simulate so (f <$> oa) s).support =
  prod.map f id '' (simulate so oa s).support :=
set.ext (λ x, by simp only [@eq_comm, simulate_map, support_bind, support_return,
  set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_image])

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support -/
theorem support_simulate_subset_preimage_support :
  (simulate so oa s).support ⊆ prod.fst ⁻¹' oa.support :=
begin
  rw [set.preimage],
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [simulate_return, support_return, set.mem_singleton_iff,
      set.singleton_subset_iff, set.mem_set_of_eq] },
  { rw [support_simulate_bind],
    refine set.Union_subset (λ x, set.Union_subset (λ hx, _)),
    simp only [support_bind, set.mem_Union, exists_prop],
    refine λ b hb, ⟨x.1, hoa s hx, hob x.1 x.2 hb⟩ },
  { simp only [support_query, set.top_eq_univ, set.mem_univ, set.set_of_true, set.subset_univ] }
end

lemma mem_support_of_mem_support_simulate {x : α × so.S} (hx : x ∈ (simulate so oa s).support) :
  x.1 ∈ oa.support := support_simulate_subset_preimage_support so oa s hx

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

lemma eval_dist_simulate_return : ⦃simulate so (return a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate_pure' : ⦃simulate so (pure' α a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_dist_simulate_pure : ⦃simulate so (pure a) s⦄ = pmf.pure (a, s) := rfl

@[simp]
lemma eval_dist_simulate_bind :
  ⦃simulate so (oa >>= ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
(congr_arg _ $ simulate_bind so oa ob s).trans (eval_dist_bind _ _)

lemma eval_dist_simulate_bind' :
  ⦃simulate so (bind' α β oa ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
eval_dist_simulate_bind so oa ob s

lemma eval_dist_simulate_query : ⦃simulate so (query i t) s⦄ = ⦃so i (t, s)⦄ := rfl

@[simp]
lemma eval_dist_simulate_map :
  ⦃simulate so (f <$> oa) s⦄ = ⦃simulate so oa s⦄.map (prod.map f id) :=
by simpa only [simulate_map, eval_dist_bind, eval_dist_return]

end eval_dist

section equiv

lemma simulate_return_equiv : simulate so (return a) s ≃ₚ
  (return (a, s) : oracle_comp spec' (α × so.S)) := rfl

lemma simulate_pure'_equiv : simulate so (pure' α a) s ≃ₚ
  (return (a, s) : oracle_comp spec' (α × so.S)) := rfl

lemma simulate_pure_equiv : simulate so (pure a) s ≃ₚ
  (pure (a, s) : oracle_comp spec' (α × so.S)) := rfl

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
def simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec α) (s : so.S) :
  oracle_comp spec' α := prod.fst <$> oa.simulate so s

lemma simulate'_def : simulate' so oa s = prod.fst <$> oa.simulate so s := rfl

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
  simulate so oa s >>= return ∘ prod.map f id >>= return ∘ prod.fst := rfl

section support

@[simp]
lemma support_simulate' : (simulate' so oa s).support =
  prod.fst '' (simulate so oa s).support :=
by simp only [simulate', support_map]

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

@[simp]
lemma support_simulate'_map : (simulate' so (f <$> oa) s).support =
  f '' (simulate' so oa s).support :=
by simp only [simulate', support_map, support_simulate_map, set.image_image, prod.map_fst]

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support -/
lemma support_simulate'_subset_support : (simulate' so oa s).support ⊆ oa.support :=
begin
  refine (support_simulate' so oa s).symm ▸ λ x hx, _,
  obtain ⟨y, hy, rfl⟩ := (set.mem_image prod.fst _ _).1 hx,
  exact mem_support_of_mem_support_simulate so oa s hy,
end

lemma mem_support_of_mem_support_simulate' {x : α} (hx : x ∈ (simulate' so oa s).support) :
  x ∈ oa.support :=
(support_simulate'_subset_support so oa s hx)

#check group

theorem support_simulate'_eq_support_
  (h : ∀ i t s, prod.fst '' (so i (t, s)).support = ⊤) :
  (simulate' so oa s).support = oa.support :=
begin
  refine set.eq_of_subset_of_subset (support_simulate'_subset_support so oa s) (λ x hx, _),
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simpa only [simulate'_return, support_map, support_return, set.image_singleton] using hx },
  { simp only [support_simulate'_bind, support_bind, set.mem_Union] at hx ⊢,
    obtain ⟨a, ha, hx⟩ := hx,
    specialize hoa a ha s,
    rw [support_simulate', set.mem_image] at hoa,
    obtain ⟨⟨a', s'⟩, ha', ha''⟩ := hoa,
    exact ⟨(a', s'), ha', hob a' x (let this : a = a' := ha''.symm in this ▸ hx) s'⟩ },
  { simp only [support_simulate'_query, set.mem_image],
    have : x ∈ prod.fst '' (so i (t, s)).support := (h i t s).symm ▸ set.mem_univ _,
    exact (set.mem_image _ _ _).1 this }
end

/-- If the first output of an oracle can take on any value (although the state might not),
then the first value of simulation has the same support as the original computation.
For example simulation with the identity oracle `idₛ` doesn't change the support,
  and this also holds for something like a logging oracle that just records queries -/
theorem support_simulate'_eq_support (h : ∀ i t s, prod.fst '' (so i (t, s)).support = ⊤) :
  (simulate' so oa s).support = oa.support :=
begin
  refine set.eq_of_subset_of_subset (support_simulate'_subset_support so oa s) (λ x hx, _),
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simpa only [simulate'_return, support_map, support_return, set.image_singleton] using hx },
  { simp only [support_simulate'_bind, support_bind, set.mem_Union] at hx ⊢,
    obtain ⟨a, ha, hx⟩ := hx,
    specialize hoa a ha s,
    rw [support_simulate', set.mem_image] at hoa,
    obtain ⟨⟨a', s'⟩, ha', ha''⟩ := hoa,
    exact ⟨(a', s'), ha', hob a' x (let this : a = a' := ha''.symm in this ▸ hx) s'⟩ },
  { simp only [support_simulate'_query, set.mem_image],
    have : x ∈ prod.fst '' (so i (t, s)).support := (h i t s).symm ▸ set.mem_univ _,
    exact (set.mem_image _ _ _).1 this }
end

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

@[simp]
lemma eval_dist_simulate' : ⦃simulate' so oa s⦄ = ⦃simulate so oa s⦄.map prod.fst :=
eval_dist_map _ prod.fst

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

lemma eval_dist_simulate'_bind' : ⦃simulate' so (bind' α β oa ob) s⦄ =
  ⦃simulate so oa s⦄.bind (λ x, ⦃simulate' so (ob x.1) x.2⦄) := eval_dist_simulate'_bind _ _ _ s

lemma eval_dist_simulate'_query : ⦃simulate' so (query i t) s⦄ = ⦃so i (t, s)⦄.map prod.fst :=
by simp only [simulate'_query, eval_dist_map]

@[simp]
lemma eval_dist_simulate'_map : ⦃simulate' so (f <$> oa) s⦄ = ⦃simulate' so oa s⦄.map f :=
by simp_rw [eval_dist_simulate', eval_dist_simulate_map,
  pmf.map_comp, prod.map_fst']

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