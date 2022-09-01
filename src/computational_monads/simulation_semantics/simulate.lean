import computational_monads.distribution_semantics.prob_event

namespace oracle_comp

-- TODO: α β γ

-- TODO: ∈ / mem versions of lemmas
variables {α β γ : Type} {spec spec' spec'' : oracle_spec}

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle
  
  `default_state` can be provided as a standard initial state for simulation.
  Used when calling `default_simulate` or `default_simulate'` -/
structure simulation_oracle (spec spec' : oracle_spec) :=
(S : Type)
(default_state : S)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

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
| _ (query i t) state := so.o i (t, state)

@[simp]
lemma simulate_return : simulate so (return a) s = return (a, s) := rfl

lemma simulate_pure' : simulate so (pure' α a) s = return (a, s) := rfl

lemma simulate_pure : simulate so (pure a) s = return (a, s) := rfl

@[simp]
lemma simulate_bind : simulate so (oa >>= ob) s =
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma simulate_bind' : simulate so (bind' α β oa ob) s =
  simulate so oa s >>= λ x, simulate so (ob x.1) x.2 := rfl

@[simp]
lemma simulate_query : simulate so (query i t) s = so.o i (t, s) := rfl

@[simp]
lemma simulate_map : simulate so (f <$> oa) s =
  simulate so oa s >>= return ∘ prod.map f id := rfl

section support

lemma support_simulate_return : (simulate so (return a) s).support = {(a, s)} := rfl

lemma support_simulate_pure' : (simulate so (pure' α a) s).support = {(a, s)} := rfl

lemma support_simulate_pure : (simulate so (pure a) s).support = {(a, s)} := rfl

lemma support_simulate_bind : (simulate so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_simulate_bind' : (simulate so (bind' α β oa ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_simulate_query : (simulate so (query i t) s).support = (so.o i (t, s)).support := rfl

@[simp]
lemma support_simulate_map : (simulate so (f <$> oa) s).support =
  prod.map f id '' (simulate so oa s).support :=
set.ext (λ x, by simp only [@eq_comm, simulate_map, support_bind, support_return,
  set.mem_Union, set.mem_singleton_iff, exists_prop, set.mem_image])

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support -/
theorem support_simulate_subset_support : (simulate so oa s).support ⊆ {x | x.1 ∈ oa.support} :=
begin
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
  x.1 ∈ oa.support := support_simulate_subset_support so oa s hx

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_distribution

lemma eval_distribution_simulate_return : ⦃simulate so (return a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_distribution_simulate_pure' : ⦃simulate so (pure' α a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_distribution_simulate_pure : ⦃simulate so (pure a) s⦄ = pmf.pure (a, s) := rfl

lemma eval_distribution_simulate_bind :
  ⦃simulate so (oa >>= ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
by rw [simulate_bind, eval_distribution_bind]

lemma eval_distribution_simulate_bind' :
  ⦃simulate so (bind' α β oa ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
by rw [simulate_bind', eval_distribution_bind]

lemma eval_distribution_simulate_query :
  ⦃simulate so (query i t) s⦄ = ⦃so.o i (t, s)⦄ := rfl

@[simp]
lemma eval_distribution_simulate_map :
  ⦃simulate so (f <$> oa) s⦄ = ⦃simulate so oa s⦄.map (prod.map f id) :=
by simpa only [simulate_map, eval_distribution_bind, eval_distribution_return]

end eval_distribution

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

lemma simulate_query_equiv : simulate so (query i t) s ≃ₚ so.o i (t, s) := rfl

@[simp]
lemma simulate_map_equiv (f : α → β) : simulate so (f <$> oa) s ≃ₚ
  prod.map f id <$> simulate so oa s :=
by simpa only [simulate_map, eval_distribution_bind, eval_distribution_map]

end equiv

end distribution_semantics

end simulate

section simulate'

/-- Get the result of simulation without returning the internal oracle state -/
def simulate' (so : simulation_oracle spec spec') (oa : oracle_comp spec α) (s : so.S) :
  oracle_comp spec' α := prod.fst <$> oa.simulate so s

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
lemma simulate'_query : simulate' so (query i t) s = prod.fst <$> so.o i (t, s) := rfl

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

lemma support_simulate'_bind : (simulate' so (oa >>= ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
by simp only [set.image_Union, simulate'_bind, support_map, support_bind, support_simulate']

lemma support_simulate'_bind' : (simulate' so (bind' α β oa ob) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate' so (ob $ prod.fst x) x.snd).support :=
support_simulate'_bind so oa ob s

lemma support_simulate'_query : (simulate' so (query i t) s).support =
  prod.fst '' (so.o i (t, s)).support := by simp only [simulate'_query, support_map]

@[simp]
lemma support_simulate'_map : (simulate' so (f <$> oa) s).support =
  f '' (simulate' so oa s).support :=
by simp only [simulate', support_map, support_simulate_map, set.image_image, prod.map_fst]

@[simp]
lemma support_simulate'_subset_support : (simulate' so oa s).support ⊆ oa.support :=
begin
  refine (support_simulate' so oa s).symm ▸ λ x hx, _,
  obtain ⟨y, hy, rfl⟩ := (set.mem_image prod.fst _ _).1 hx,
  exact mem_support_of_mem_support_simulate so oa s hy,
end

/-- If the first output of an oracle can take on any value (although the state might not),
  then the first value of simulation has the same support as the original computation.
  For example simulation with the identity oracle `idₛ` doesn't change the support
  TODO: cleanup -/
theorem support_simulate'_eq_support (h : ∀ i t s, prod.fst '' (so.o i (t, s)).support = ⊤) :
  (simulate' so oa s).support = oa.support :=
begin
  refine set.eq_of_subset_of_subset (support_simulate'_subset_support so oa s) (λ x hx, _),
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simpa only [simulate'_return, support_map, support_return, set.image_singleton] using hx },
  {
    simp only [support_simulate'_bind, support_bind, set.mem_Union] at hx ⊢,
    obtain ⟨a, ha, hx⟩ := hx,
    specialize hoa a ha s,
    rw [support_simulate', set.mem_image] at hoa,
    obtain ⟨⟨a', s'⟩, ha', ha''⟩ := hoa,
    refine ⟨(a', s'), ha', hob a' x _ s'⟩,
    rw ← ha'' at hx,
    exact hx,
  },
  { simp only [support_simulate'_query, set.mem_image],
    specialize h i t s,
    have : x ∈ prod.fst '' (so.o i (t, s)).support := h.symm ▸ set.mem_univ _,
    rw [set.mem_image] at this,
    exact this }
end

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_distribution

@[simp]
lemma eval_distribution_simulate' : ⦃simulate' so oa s⦄ = prod.fst <$> ⦃simulate so oa s⦄ :=
eval_distribution_map _ prod.fst

lemma eval_distribution_simulate'_return : ⦃simulate' so (return a) s⦄ = pmf.pure a :=
by simp only [simulate'_return, map_return_equiv, eval_distribution_return]

lemma eval_distribution_simulate'_pure' : ⦃simulate' so (pure' α a) s⦄ = pmf.pure a :=
eval_distribution_simulate'_return so a s

lemma eval_distribution_simulate'_pure : ⦃simulate' so (pure a) s⦄ = pmf.pure a :=
eval_distribution_simulate'_return so a s

lemma eval_distribution_simulate'_bind :
  ⦃simulate' so (oa >>= ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate' so (ob x.1) x.2⦄ :=
by simp [simulate']

lemma eval_distribution_simulate'_bind' :
  ⦃simulate' so (bind' α β oa ob) s⦄ = ⦃simulate so oa s⦄ >>= λ x, ⦃simulate' so (ob x.1) x.2⦄ :=
eval_distribution_simulate'_bind so oa ob s

lemma eval_distribution_simulate'_query :
  ⦃simulate' so (query i t) s⦄ = prod.fst <$> ⦃so.o i (t, s)⦄ :=
by simpa only [simulate'_query, eval_distribution_map]

@[simp]
lemma eval_distribution_simulate'_map :
  ⦃simulate' so (f <$> oa) s⦄ = ⦃simulate' so oa s⦄.map f :=
by simp_rw [eval_distribution_simulate', eval_distribution_simulate_map,
  pmf.monad_map_eq_map, pmf.map_comp, prod.map_fst']

end eval_distribution

@[simp]
lemma simulate'_equiv_fst_map_simulate :
  simulate' so oa s ≃ₚ prod.fst <$> simulate so oa s := rfl

lemma simulate'_return_equiv : simulate' so (return a) s ≃ₚ
  (return a : oracle_comp spec' α) := by simp only [simulate'_return, map_return_equiv]

lemma simulate'_pure'_equiv : simulate' so (pure' α a) s ≃ₚ
  (return a : oracle_comp spec' α) := simulate'_return_equiv so a s

lemma simulate'_pure_equiv : simulate' so (pure a) s ≃ₚ
  (return a : oracle_comp spec' α) := simulate'_return_equiv so a s

@[simp]
lemma simulate'_bind_equiv : simulate' so (oa >>= ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 :=
by simp only [simulate'_equiv_fst_map_simulate, simulate_bind, map_bind_equiv,
  eval_distribution_bind, simulate'_equiv_fst_map_simulate]

lemma simulate'_bind'_equiv : simulate' so (bind' α β oa ob) s ≃ₚ
  simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 :=
simulate'_bind_equiv so oa ob s

@[simp]
lemma simulate'_query_equiv : simulate' so (query i t) s ≃ₚ
  prod.fst <$> (so.o i (t, s)) := rfl

@[simp]
lemma simulate'_map_equiv (f : α → β) : simulate' so (f <$> oa) s ≃ₚ f <$> simulate' so oa s :=
by simp only [simulate_map_equiv, eval_distribution_map, pmf.map_comp,
  prod.map_fst', simulate'_equiv_fst_map_simulate]

-- -- TODO: other versions of this
-- lemma simulate'_equiv_of_equiv [spec.finite_range] {oa oa' : oracle_comp spec α} (h : oa ≃ₚ oa') :
--   simulate' so oa s ≃ₚ simulate' so oa' s :=
-- begin
  
-- end

end distribution_semantics

end simulate'

end oracle_comp