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

-- TODO: this file is long as hell, maybe a whole simulate folder? `basic` `subsingleton` `induction` etc.
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

def inhabited_state (so : sim_oracle spec spec' S) : inhabited S := ⟨so.default_state⟩

lemma has_coe_to_fun_def (so : sim_oracle spec spec' S) (i : spec.ι)
  (x : spec.domain i × S) : so i x = so.o i x := rfl

end sim_oracle

namespace oracle_comp

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
variables (a : α) (i : spec.ι) (t : spec.domain i)
  (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) (s : S) (f : α → β)

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

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind` -/
lemma support_simulate_eq_induction {supp : Π (α : Type), oracle_comp spec α → S → set (α × S)}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, supp α (return a) s = {(a, s)})
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    supp β (oa >>= ob) s = ⋃ x ∈ (supp α oa s), supp β (ob $ prod.fst x) $ prod.snd x)
  (h_query : ∀ i t s, supp (spec.range i) (query i t) s = (so i (t, s)).support) :
  (simulate so oa s).support = supp α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate_return, support_return] },
  { simp only [simulate_bind, support_bind, hoa, hob, h_bind] },
  { simp only [h_query, simulate_query] }
end

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

lemma eval_dist_simulate_bind_apply (x : β × S) : ⦃simulate so (oa >>= ob) s⦄ x
  = ∑' (a : α) (s' : S), ⦃simulate so oa s⦄ (a, s') * ⦃simulate so (ob a) s'⦄ x :=
begin
  rw [eval_dist_simulate_bind, pmf.bind_apply],
  refine tsum_prod' (nnreal.summable_of_le (λ x, mul_le_of_le_of_le_one le_rfl
    (pmf.apply_le_one _ _)) (pmf.summable_coe ⦃simulate so oa s⦄)) (λ a, _),
  have : summable (λ s', ⦃simulate so oa s⦄ (a, s')),
  from nnreal.summable_comp_injective (pmf.summable_coe ⦃simulate so oa s⦄)
    (λ s s' hs, (prod.eq_iff_fst_eq_snd_eq.1 hs).2),    refine nnreal.summable_of_le _ this,
  exact λ s, mul_le_of_le_of_le_one le_rfl (pmf.apply_le_one _ _)
end

lemma eval_dist_simulate_bind' : ⦃simulate so (bind' α β oa ob) s⦄ =
  (⦃simulate so oa s⦄).bind (λ x, ⦃simulate so (ob x.1) x.2⦄) :=
eval_dist_simulate_bind so oa ob s

lemma eval_dist_simulate_query : ⦃simulate so (query i t) s⦄ = ⦃so i (t, s)⦄ := rfl

lemma eval_dist_simulate_map : ⦃simulate so (f <$> oa) s⦄ =
  ⦃simulate so oa s⦄.map (prod.map f id) := by rw [simulate_map, eval_dist_map]

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind` -/
lemma eval_dist_simulate_eq_induction {pr : Π (α : Type), oracle_comp spec α → S → (pmf (α × S))}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, pr α (return a) s = pmf.pure (a, s))
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    pr β (oa >>= ob) s = (pr α oa s).bind (λ x, pr β (ob x.1) x.2))
  (h_query : ∀ i t s, pr (spec.range i) (query i t) s = ⦃so i (t, s)⦄) :
  ⦃simulate so oa s⦄ = pr α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a' α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate_return, eval_dist_return] },
  { simp only [h_bind, hoa, hob, simulate_bind, eval_dist_bind] },
  { simp only [h_query, simulate_query] }
end

/-- Lemma for inductively proving that the distribution associated to a simulation
is a specific function. Gives more explicit criteria than induction on the computation.
In particular this automatically splits the cases for `return` and the `prod` in the `bind` sum. -/
lemma eval_dist_simulate_apply_eq_induction
  {pr : Π (α : Type), oracle_comp spec α → S → α × S → ℝ≥0}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S) (a : α) (s' : S)
  (h_ret : ∀ α a s, pr α (return a) s (a, s) = 1)
  (h_ret' : ∀ α a a' s s', a ≠ a' ∨ s ≠ s' → pr α (return a) s (a', s') = 0)
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s b s',
    pr β (oa >>= ob) s (b, s') = ∑' (a : α) (t : S), (pr α oa s (a, t)) * (pr β (ob a) t (b, s')))
  (h_query : ∀ i t s u s', pr (spec.range i) (query i t) s (u, s') = ⦃so i (t, s)⦄ (u, s')) :
  ⦃simulate so oa s⦄ (a, s') = pr α oa s (a, s') :=
begin 
  induction oa using oracle_comp.induction_on with α a' α β oa ob hoa hob i t generalizing s s',
  { rw [eval_dist_simulate_return, pmf.pure_apply],
    split_ifs with has,
    { simp only [prod.eq_iff_fst_eq_snd_eq] at has,
      refine has.1 ▸ has.2.symm ▸ (h_ret α a s).symm, },
    { simp only [prod.eq_iff_fst_eq_snd_eq, not_and_distrib] at has,
      cases has with ha hs,
      { exact (h_ret' α a' a s s' $ or.inl $ ne.symm ha).symm },
      { exact (h_ret' α a' a s s' $ or.inr $ ne.symm hs).symm } } },
  { simp only [eval_dist_simulate_bind_apply, h_bind, hoa, hob] },
  { rw [eval_dist_simulate_query, h_query] },
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

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support -/
lemma support_simulate'_subset_support : (simulate' so oa s).support ⊆ oa.support :=
begin
  refine (support_simulate' so oa s).symm ▸ λ x hx, _,
  obtain ⟨y, hy, rfl⟩ := (set.mem_image prod.fst _ _).1 hx,
  exact support_simulate_subset_preimage_support so oa s hy,
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
  { simp only [support_simulate'_query, h i t s] }
end

theorem support_simulate'_eq_support_simulate'
  {so : sim_oracle spec spec' S} {so' : sim_oracle spec spec' S'}
  (h : ∀ i t s s', prod.fst '' (so i (t, s)).support = prod.fst '' (so' i (t, s')).support)
  (oa : oracle_comp spec α) (s : S) (s' : S') :
  (simulate' so oa s).support = (simulate' so' oa s').support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s s',
  { simp only [simulate'_return, support_map, support_return, set.image_singleton] },
  { ext x,
    simp_rw [support_simulate'_bind, set.mem_Union],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨⟨a, t⟩, hoa', hob'⟩ := h,
      have : ∃ u, (a, u) ∈ (simulate so oa s).support := ⟨t, hoa'⟩,
      rw [← mem_support_simulate'_iff_exists_state, hoa s s',
        mem_support_simulate'_iff_exists_state] at this,
      obtain ⟨t', ht'⟩ := this,
      exact ⟨(a, t'), ht', hob a t t' ▸ hob'⟩ },
    -- TODO: This is basically the same as the above, maybe simplify somehow
    { obtain ⟨⟨a, t⟩, hoa', hob'⟩ := h,
      have : ∃ u, (a, u) ∈ (simulate so' oa s').support := ⟨t, hoa'⟩,
      rw [← mem_support_simulate'_iff_exists_state, ← hoa s s',
        mem_support_simulate'_iff_exists_state] at this,
      obtain ⟨t', ht'⟩ := this,
      exact ⟨(a, t'), ht', (hob a t' t).symm ▸ hob'⟩ } },
  { simpa only [support_simulate'_query] using h i t s s' }
end

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
    by simp_rw [eval_dist_simulate'_apply, eval_dist_simulate_bind_apply]
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

/-- If the first result of oracle queries is uniformly distributed,
then the distribution under `simulate'` is unchanged. -/
theorem eval_dist_simulate'_eq_eval_dist [spec.finite_range]
  (h : ∀ i t s, ⦃so i (t, s)⦄.map prod.fst = pmf.uniform_of_fintype (spec.range i)) :
  ⦃simulate' so oa s⦄ = ⦃oa⦄ :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [simulate'_return, map_return_equiv, eval_dist_return] },
  { 
    refine pmf.ext (λ b, _),
    rw [eval_dist_bind_apply, eval_dist_simulate'_bind_apply],
    refine tsum_congr (λ a, _),
    rw [← hoa s],
    rw [eval_dist_simulate'_apply, ← nnreal.tsum_mul_right],
    refine tsum_congr (λ t, _),
    rw ← hob,
  },
  { simp only [h, simulate'_query, eval_dist_map, eval_dist_query] }
end

theorem eval_dist_simulate'_eq_eval_dist_simulate' : sorry := sorry

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

-- Lemmas about the state being `subsingleton` (although this necessarilly implies `unique`).
-- Main use cases are for things like `stateless_oracle`
section subsingleton_state

section support

/-- Reduce to the default state for oracles with a subsingleton state type -/
@[simp]
lemma support_simulate_eq_support_default_simulate [subsingleton S] (s : S) :
  (simulate so oa s).support = (default_simulate so oa).support :=
subsingleton.elim so.default_state s ▸ rfl


/-- Version of `support_simulate'_eq_support` for `default_simulate`, given a `subsingleton` state.
Has a weaker requirement for the hypothesis `h` that the more general lemma -/
theorem support_default_simulate'_eq_support [subsingleton S]
  (h : ∀ i t, prod.fst '' (so i (t, so.default_state)).support = ⊤) :
  (default_simulate' so oa).support = oa.support :=
support_simulate'_eq_support so oa so.default_state
  (λ i t s, subsingleton.elim so.default_state s ▸ h i t)

/-- If the state is a `subsingleton` type, suffices to use the support with `default_state` -/
lemma support_simulate'_eq_support_default_simulate' [subsingleton S] (s : S) :
  (simulate' so oa s).support = (default_simulate' so oa).support :=
subsingleton.elim so.default_state s ▸ rfl

/-- Given the state is `subsingleton`, the support of `simulate` is determined by `simulate'` -/
lemma support_simulate_eq_image_support_simulate' [subsingleton S] :
  (simulate so oa s).support = (λ x, (x, so.default_state)) '' (default_simulate' so oa).support :=
begin
  have : (λ (x : α × S), (x.fst, so.default_state)) = id,
  from funext (λ x, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, subsingleton.elim _ x.2⟩),
  rw [support_simulate', set.image_image, this, set.image_id,
    support_simulate_eq_support_default_simulate],
end

/-- Given the state is `subsingleton`, membership in `support` of `simulate` can be checked
by just checking that the first component is in the support of `simulate'` -/
lemma mem_support_simulate_iff_fst_mem_support_simulate' (x : α × S) [subsingleton S] :
  x ∈ (simulate so oa s).support ↔ x.fst ∈ (simulate' so oa s).support :=
begin
  refine subsingleton.elim so.default_state s ▸ _,
  rw [support_simulate_eq_image_support_simulate', set.mem_image],
  exact ⟨λ h, let ⟨a, ha, hax⟩ := h in hax ▸ ha, λ h, ⟨x.1, h, prod.eq_iff_fst_eq_snd_eq.2
    ⟨rfl, subsingleton.elim x.2 so.default_state ▸ rfl⟩⟩⟩
end

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

@[simp]
lemma eval_dist_simulate_eq_eval_dist_default_simulate [subsingleton S] (s : S) :
  ⦃simulate so oa s⦄ = ⦃default_simulate so oa⦄ := subsingleton.elim so.default_state s ▸ rfl

lemma eval_dist_simulate'_eq_eval_dist_default_simulate' [subsingleton S] (s : S) :
  ⦃simulate' so oa s⦄ = ⦃default_simulate' so oa⦄ := subsingleton.elim so.default_state s ▸ rfl

end eval_dist

section equiv

lemma simulate_equiv_default_simulate [subsingleton S] (s : S) :
  simulate so oa s ≃ₚ default_simulate so oa := subsingleton.elim so.default_state s ▸ rfl

lemma simulate'_equiv_default_simulate' [subsingleton S] (s : S) :
  simulate' so oa s ≃ₚ default_simulate' so oa := subsingleton.elim so.default_state s ▸ rfl

end equiv

section prob_event

end prob_event

end distribution_semantics

end subsingleton_state

end oracle_comp