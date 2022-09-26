import computational_monads.simulation_semantics.simulate

namespace oracle_comp

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
  (a : α) (i : spec.ι) (t : spec.domain i)
  (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) (f : α → β)

section default_simulate

-- TODO: should this go farther and be `notation` instead of `inline`?
@[inline, reducible]
def default_simulate (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' (α × S) := oa.simulate so so.default_state

lemma default_simulate_return : default_simulate so (return a) = pure (a, so.default_state) := rfl

lemma default_simulate_pure' : default_simulate so (pure' α a) = pure (a, so.default_state) := rfl

lemma default_simulate_pure : default_simulate so (pure a) = pure (a, so.default_state) := rfl

lemma default_simulate_bind : default_simulate so (oa >>= ob) =
  simulate so oa so.default_state >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma default_simulate_bind' : default_simulate so (bind' α β oa ob) =
  simulate so oa so.default_state >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma default_simulate_query : default_simulate so (query i t) =
  so i (t, so.default_state) := rfl

lemma default_simulate_map : default_simulate so (f <$> oa) =
  simulate so oa so.default_state >>= return ∘ prod.map f id := rfl

section support

/-- Reduce to the default state for oracles with a subsingleton state type -/
@[simp]
lemma support_simulate_eq_support_default_simulate [subsingleton S] (s : S) :
  (simulate so oa s).support = (default_simulate so oa).support :=
subsingleton.elim so.default_state s ▸ rfl

lemma support_default_simulate_return : (default_simulate so (return a)).support =
  {(a, so.default_state)} := rfl

lemma support_default_simulate_pure' : (default_simulate so (pure' α a)).support =
  {(a, so.default_state)} := rfl

lemma support_default_simulate_pure : (default_simulate so (pure a)).support =
  {(a, so.default_state)} := rfl

lemma support_default_simulate_bind : (default_simulate so (oa >>= ob)).support =
  ⋃ x ∈ (default_simulate so oa).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_default_simulate_bind' : (default_simulate so (bind' α β oa ob)).support =
  ⋃ x ∈ (default_simulate so oa).support, (simulate so (ob $ prod.fst x) x.2).support := rfl

lemma support_default_simulate_query : (default_simulate so (query i t)).support =
  (so i (t, so.default_state)).support := rfl

lemma support_default_simulate_map : (default_simulate so (f <$> oa)).support =
  prod.map f id '' (default_simulate so oa).support := support_simulate_map so oa _ f

lemma support_default_simulate_subset_support :
  (default_simulate so oa).support ⊆ prod.fst ⁻¹' oa.support :=
support_simulate_subset_preimage_support so oa so.default_state

lemma mem_support_of_mem_support_default_simulate {x : α × S}
  (hx : x ∈ (default_simulate so oa).support) : x.1 ∈ oa.support :=
mem_support_of_mem_support_simulate so oa so.default_state hx

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

@[simp]
lemma eval_dist_simulate_eq_eval_dist_default_simulate [subsingleton S] (s : S) :
  ⦃simulate so oa s⦄ = ⦃default_simulate so oa⦄ := subsingleton.elim so.default_state s ▸ rfl

lemma eval_dist_deault_simulate_return :
  ⦃default_simulate so (return a)⦄ = pmf.pure (a, so.default_state) := rfl

lemma eval_dist_default_simulate_pure' :
  ⦃default_simulate so (pure' α a)⦄ = pmf.pure (a, so.default_state) := rfl

lemma eval_dist_default_simulate_pure :
  ⦃default_simulate so (pure a)⦄ = pmf.pure (a, so.default_state) := rfl

lemma eval_dist_default_simulate_bind : ⦃default_simulate so (oa >>= ob)⦄ =
  ⦃simulate so oa so.default_state⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
eval_dist_simulate_bind so oa ob so.default_state

lemma eval_dist_default_simulate_bind' : ⦃default_simulate so (bind' α β oa ob)⦄ =
  ⦃simulate so oa so.default_state⦄ >>= λ x, ⦃simulate so (ob x.1) x.2⦄ :=
eval_dist_simulate_bind so oa ob so.default_state

lemma eval_dist_default_simulate_query :
  ⦃default_simulate so (query i t)⦄ = ⦃so i (t, so.default_state)⦄ :=
eval_dist_simulate_query so i t so.default_state

lemma eval_dist_default_simulate_map :
  ⦃default_simulate so (f <$> oa)⦄ = ⦃simulate so oa so.default_state⦄.map (prod.map f id) :=
eval_dist_simulate_map so oa so.default_state f

end eval_dist

section equiv

lemma simulate_equiv_default_simulate [subsingleton S] (s : S) :
  simulate so oa s ≃ₚ default_simulate so oa := subsingleton.elim so.default_state s ▸ rfl

lemma default_simulate_return_equiv : default_simulate so (return a) ≃ₚ
  (pure (a, so.default_state) : oracle_comp spec' (α × S)) := rfl

lemma default_simulate_pure'_equiv : default_simulate so (pure' α a) ≃ₚ
  (pure (a, so.default_state) : oracle_comp spec' (α × S)) := rfl

lemma default_simulate_pure_equiv : default_simulate so (pure a) ≃ₚ
  (pure (a, so.default_state) : oracle_comp spec' (α × S)) := rfl

lemma default_simulate_bind_equiv : default_simulate so (oa >>= ob) ≃ₚ
  default_simulate so oa >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma default_simulate_bind'_equiv : default_simulate so (bind' α β oa ob) ≃ₚ
  default_simulate so oa >>= λ x, simulate so (ob x.1) x.2 := rfl

lemma default_simulate_query_equiv : default_simulate so (query i t) ≃ₚ
  so i (t, so.default_state) := rfl

lemma default_simulate_map_equiv : default_simulate so (f <$> oa) ≃ₚ
  prod.map f id <$> simulate so oa so.default_state := simulate_map_equiv so oa _ f

end equiv

end distribution_semantics

end default_simulate

section default_simulate'

@[inline, reducible]
def default_simulate' (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) :
  oracle_comp spec' α := oa.simulate' so so.default_state

lemma default_simulate'_return : default_simulate' so (return a) =
  prod.fst <$> return (a, so.default_state) := rfl

lemma default_simulate'_pure' : default_simulate' so (pure' α a) =
  prod.fst <$> return (a, so.default_state) := rfl

lemma default_simulate'_pure : default_simulate' so (pure a) =
  prod.fst <$> pure (a, so.default_state) := rfl

lemma default_simulate'_bind : default_simulate' so (oa >>= ob) =
  prod.fst <$> (default_simulate so oa >>= λ x, simulate so (ob x.1) x.2) := rfl

lemma default_simulate'_bind' : default_simulate' so (bind' α β oa ob) =
  prod.fst <$> (default_simulate so oa >>= λ x, simulate so (ob x.1) x.2) := rfl

lemma default_simulate'_query : default_simulate' so (query i t) =
  prod.fst <$>so i (t, so.default_state) := rfl

section support

lemma support_simulate'_eq_support_default_simulate' [subsingleton S] (s : S) :
  (simulate' so oa s).support = (default_simulate' so oa).support :=
subsingleton.elim so.default_state s ▸ rfl

lemma support_default_simulate'_return : (default_simulate' so (return a)).support = {a} :=
support_simulate'_return so so.default_state a

lemma support_default_simulate'_pure' : (default_simulate' so (pure' α a)).support = {a} :=
support_simulate'_return so so.default_state a

lemma support_default_simulate'_pure : (default_simulate' so (pure a)).support = {a} :=
support_simulate'_return so so.default_state a

lemma support_default_simulate'_bind : (default_simulate' so (oa >>= ob)).support =
  ⋃ a ∈ (default_simulate so oa).support, (simulate' so (ob $ prod.fst a) a.2).support :=
by simp [set.image_Union]

lemma support_default_simulate'_query : (default_simulate' so (query i t)).support =
  prod.fst '' (so i (t, so.default_state)).support := support_simulate'_query so i t _

lemma support_default_simulate'_map : (default_simulate' so (f <$> oa)).support =
  f '' (simulate' so oa so.default_state).support :=
support_simulate'_map so oa so.default_state f

lemma support_default_simulate'_subset_support : (default_simulate' so oa).support ⊆ oa.support :=
support_simulate'_subset_support so oa so.default_state

lemma mem_support_of_mem_support_default_simulate' {x : α}
  (hx : x ∈ (default_simulate' so oa).support) : x ∈ oa.support :=
mem_support_of_mem_support_simulate' so oa so.default_state hx

/-- If the first output of an oracle can take on any value (although the state might not),
then the first value of simulation has the same support as the original computation.
For example simulation with the identity oracle `idₛ` doesn't change the support -/
theorem support_default_simulate'_eq_support [subsingleton S]
  (h : ∀ i t, prod.fst '' (so i (t, so.default_state)).support = ⊤) :
  (default_simulate' so oa).support = oa.support :=
support_simulate'_eq_support so oa so.default_state
  (λ i t s, subsingleton.elim so.default_state s ▸ h i t)

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

lemma eval_dist_simulate'_eq_eval_dist_default_simulate' [subsingleton S] (s : S) :
  ⦃simulate' so oa s⦄ = ⦃default_simulate' so oa⦄ := subsingleton.elim so.default_state s ▸ rfl

lemma eval_dist_default_simulate'_return : ⦃default_simulate' so (return a)⦄ =
  pmf.pure a := eval_dist_simulate'_return so a _

lemma eval_dist_default_simulate'_pure' : ⦃default_simulate' so (pure' α a)⦄ =
  pmf.pure a := eval_dist_simulate'_pure so a so.default_state

lemma eval_dist_default_simulate'_pure : ⦃default_simulate' so (pure a)⦄ =
  pmf.pure a := eval_dist_simulate'_pure so a so.default_state

lemma eval_dist_default_simulate'_bind : ⦃default_simulate' so (oa >>= ob)⦄ =
  ⦃default_simulate so oa⦄.bind (λ x, ⦃simulate' so (ob x.1) x.2⦄) :=
eval_dist_simulate'_bind so oa ob so.default_state

lemma eval_dist_default_simulate'_bind' : ⦃default_simulate' so (bind' α β oa ob)⦄ =
  ⦃default_simulate so oa⦄.bind (λ x, ⦃simulate' so (ob x.1) x.2⦄) :=
eval_dist_simulate'_bind so oa ob so.default_state

lemma eval_dist_default_simulate'_query : ⦃default_simulate' so (query i t)⦄ =
  ⦃so i (t, so.default_state)⦄.map prod.fst :=
eval_dist_simulate'_query so i t so.default_state

lemma eval_dist_default_simulate'_map : ⦃default_simulate' so (f <$> oa)⦄ =
  ⦃simulate' so oa so.default_state⦄.map f :=
eval_dist_simulate'_map so oa _ f

end eval_dist

section equiv

lemma simulate'_equiv_default_simulate' [subsingleton S] (s : S) :
  simulate' so oa s ≃ₚ default_simulate' so oa := subsingleton.elim so.default_state s ▸ rfl

lemma default_simulate'_return_equiv : default_simulate' so (return a) ≃ₚ
  (pure a : oracle_comp spec' α) := 
simulate'_pure_equiv so a so.default_state

lemma default_simulate'_pure'_equiv : default_simulate' so (pure' α a) ≃ₚ
  (pure a : oracle_comp spec' α) := simulate'_pure_equiv so a so.default_state

lemma default_simulate'_pure_equiv : default_simulate' so (pure a) ≃ₚ
  (pure a : oracle_comp spec' α) := simulate'_pure_equiv so a so.default_state

lemma default_simulate'_bind_equiv : default_simulate' so (oa >>= ob) ≃ₚ
  (default_simulate so oa) >>= λ x, simulate' so (ob x.1) x.2 :=
simulate'_bind_equiv so oa ob so.default_state

lemma default_simulate'_bind'_equiv : default_simulate' so (bind' α β oa ob) ≃ₚ
  (default_simulate so oa) >>= λ x, simulate' so (ob x.1) x.2 :=
simulate'_bind_equiv so oa ob so.default_state

lemma default_simulate'_query_equiv : default_simulate' so (query i t) ≃ₚ
  prod.fst <$> (so i (t, so.default_state)) := simulate'_query_equiv so i t so.default_state

@[simp]
lemma default_simulate'_map_equiv : default_simulate' so (f <$> oa) ≃ₚ
  f <$> simulate' so oa so.default_state := simulate'_map_equiv so oa _ f

end equiv

end distribution_semantics

end default_simulate'

end oracle_comp
