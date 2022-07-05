import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}
  (oa : oracle_comp spec A)

-- TODO: use namespaces to simplify the lemma names

section tracking_oracle

/-- Oracle where the query result is indepenent of the current oracle state,
  although the new state may depend upon the previous state.
  For example a logging oracle that just tracks the input and output of queries. -/
def tracking_oracle {S : Type} (default_state : S)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S) :
  simulation_oracle spec spec' :=
{ S := S,
  default_state := default_state,
  o := λ i ⟨t, s⟩, do { u ← o i t, pure (u, update_state s i t u) } }

notation `⟪` o `|` update_state `,` default_state `⟫` :=
  tracking_oracle default_state o update_state

variables {S : Type} (default_state : S)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)

@[simp]
lemma default_state_tracking_oracle :
  (⟪o | update_state, default_state⟫).default_state = default_state := rfl

@[simp]
lemma tracking_oracle_apply (i : spec.ι) (t : spec.domain i) (s : S) :
  (⟪o | update_state, default_state⟫).o i (t, s) =
    do { u ← o i t, pure (u, update_state s i t u) } := rfl

-- TODO: should be able to find some generalization for lemmas looking like this
lemma simulate'_tracking_oracle_query_equiv [spec.finite_range]
  (s : S) : simulate' (⟪query | update_state, default_state⟫) oa s ≃ₚ oa :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { simp only [pure'_eq_pure, simulate'_pure, pure_map_equiv, eval_distribution_return] },
  { let so := ⟪query | update_state, default_state⟫,
    calc simulate' so (oa >>= ob) s
      ≃ₚ simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 : simulate'_bind_equiv _ oa ob _
      ... ≃ₚ simulate so oa s >>= λ x, (ob x.1) : bind_equiv_of_equiv_second _ (λ a _, hob a.1 _)
      ... ≃ₚ simulate' so oa s >>= ob : symm (bind_map_equiv _ prod.fst ob)
      ... ≃ₚ oa >>= ob : bind_equiv_of_equiv_first ob (hoa _) },
  { rw [eval_distribution_simulate'_equiv, tracking_oracle_apply,
      fst_map_bind_mk_equiv, map_id_equiv (query i t)], } 
end

end tracking_oracle

section stateless_oracle

/-- Simulate a computation without making use of the internal state.
  We use the `unit` type as the state in this case, so all possible states are equal.
  Implemented as a `tracking_oracle` where the state isn't actually tracking anything -/
def stateless_oracle (spec spec' : oracle_spec)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)) :
  simulation_oracle spec spec' :=
⟪o | λ _ _ _ _, (), ()⟫

notation `⟪` o `⟫` := stateless_oracle _ _ o

variables (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i))

@[simp]
lemma S_stateless_oracle :
  ⟪o⟫.S = unit := rfl

@[simp]
lemma default_state_stateless_oracle :
  ⟪o⟫.default_state = () := rfl

@[simp]
lemma stateless_oracle_apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  ⟪o⟫.o i (t, s) = o i t >>= λ u, return (u, ()) := rfl

section simulate

@[simp]
lemma support_simulate_stateless_oracle_pure (a : A) (s : unit) :
  (simulate ⟪o⟫ (pure a) s).support = {(a, ())} := by simp [punit_eq s ()]

@[simp]
lemma support_simulate_stateless_oracle_bind (oa : oracle_comp spec A)
  (ob : A → oracle_comp spec B) (s : unit) :
  (simulate ⟪o⟫ (oa >>= ob) s).support =
    ⋃ (x : A × unit) (hx : x ∈ (simulate ⟪o⟫ oa ()).support),
      (simulate ⟪o⟫ (ob x.1) x.2).support :=
begin
  refine s.rec _,
  refine (set.ext $ λ y, _),
  simp,
  sorry,
end

@[simp]
lemma support_simulate_stateless_oracle_query (i : spec.ι) (t : spec.domain i) (s : unit) :
  (simulate ⟪o⟫ (query i t) s).support = {x | x.1 ∈ (o i t).support} :=
begin
  refine s.rec _,
  simp,
  sorry,
end

end simulate

section eval_distribution

lemma simulate_stateless_oracle_equiv_simulate' [spec'.finite_range] (s : unit) :
  simulate ⟪o⟫ oa s ≃ₚ (simulate' ⟪o⟫ oa s >>= λ a, pure (a, ())) :=
calc simulate ⟪o⟫ oa s ≃ₚ simulate ⟪o⟫ oa s >>= pure : symm (bind_pure_equiv _)
  ... ≃ₚ simulate ⟪o⟫ oa s >>= λ x, pure (x.1, x.2) : by simp only [prod.mk.eta]
  ... ≃ₚ simulate ⟪o⟫ oa s >>= λ x, pure (x.1, ()) :
    bind_equiv_of_equiv_second _ (λ x _, by simp [punit_eq x.snd ()])
  ... ≃ₚ simulate' ⟪o⟫ oa s >>= λ a, pure (a, ()) : by rw [simulate', bind_map_equiv]

lemma simulate'_stateless_oracle_equiv_of_oracle_equiv [spec'.finite_range] [spec''.finite_range] 
  {o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)}
  {o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i)}
  (s : unit) (h : ∀ (i : spec.ι) (t : spec.domain i), o i t ≃ₚ o' i t) :
  simulate' ⟪o⟫ oa s ≃ₚ simulate' ⟪o'⟫ oa s :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { simp only [pure'_eq_pure, simulate'_pure, pure_map_equiv, eval_distribution_return] },
  { calc simulate' ⟪o⟫ (oa >>= ob) s
      ≃ₚ simulate ⟪o⟫ oa s >>= λ x, simulate' ⟪o⟫ (ob x.1) x.2 : simulate'_bind_equiv ⟪o⟫ oa ob _
      ... ≃ₚ simulate ⟪o'⟫ oa s >>= λ x, simulate' ⟪o'⟫ (ob x.1) x.2 : begin
        simp [simulate_stateless_oracle_equiv_simulate', hoa],
        congr,
        simpa [hob],
      end
      ... ≃ₚ simulate' ⟪o'⟫ (oa >>= ob) s : symm (simulate'_bind_equiv ⟪o'⟫ oa ob _) },
  { simp only [simulate'_query, stateless_oracle_apply, fst_map_bind_mk_equiv, map_id_equiv],
    exact h i t, }
end 

lemma simulate'_stateless_oracle_query_equiv [spec.finite_range] (s : unit) :
  simulate' ⟪query⟫ oa s ≃ₚ oa :=
simulate'_tracking_oracle_query_equiv _ _ _ _

lemma simulate'_stateless_oracle_query_equiv_of_equiv [spec.finite_range] [spec'.finite_range] (s : unit)
  (ho : ∀ (i : spec.ι) (t : spec.domain i), o i t ≃ₚ query i t) :
  simulate' ⟪o⟫ oa s ≃ₚ oa :=
calc simulate' ⟪o⟫ oa s ≃ₚ simulate' ⟪query⟫ oa s
    : simulate'_stateless_oracle_equiv_of_oracle_equiv oa s ho
  ... ≃ₚ oa : simulate'_stateless_oracle_query_equiv oa s

end eval_distribution

end stateless_oracle

section identity_oracle

def identity_oracle (spec : oracle_spec) : simulation_oracle spec spec :=
⟪ query ⟫

notation `idₛ` := identity_oracle _

@[simp]
lemma default_state_identity_oracle :
  (identity_oracle spec).default_state = () := rfl

@[simp]
lemma identity_oracle_apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  (identity_oracle spec).o i (t, s) = query i t >>= λ u, return (u, ()) := rfl

section simulate


@[simp]
lemma eval_distribution_simulate_identity_oracle [spec.finite_range] 
  (oa : oracle_comp spec A) (s : unit) :
  ⟦simulate idₛ oa s⟧ = (λ a, (a, ())) <$> ⟦oa⟧ :=
begin
  induction oa,
  {
    simp,
    sorry
  },
  sorry, sorry
end

@[simp]
lemma support_simulate_identity_oracle_pure (a : A) (s : unit) :
  (simulate idₛ (pure a : oracle_comp spec A) s).support = {(a, ())} :=
support_simulate_stateless_oracle_pure _ a s

@[simp]
lemma support_simulate_identity_oracle (oa : oracle_comp spec A) (s : unit) :
  (simulate idₛ oa s).support = {x | x.1 ∈ oa.support} :=
begin
  induction oa with A a A B oa ob hoa hob i t,
  {
    ext x,
    simp [prod.eq_iff_fst_eq_snd_eq, punit_eq x.snd s],
  },
  {
    ext x,
    simp [hoa, hob],
    sorry,
  },
  {
    ext x,
    induction x with x_fst x_snd,
    simp,
    refine punit_eq () x_snd,
  }
end

lemma mem_support_simulate_identity_oracle_iff (oa : oracle_comp spec A) (s : unit) (x : A × unit) :
  x ∈ (simulate idₛ oa s).support ↔ x.1 ∈ oa.support :=
begin
  simp,
  refine iff.rfl,
end

end simulate

section simulate'

@[simp]
lemma support_simulate'_identity_oracle (oa : oracle_comp spec A) (s : unit) :
  (simulate' idₛ oa s).support = oa.support :=
begin
  rw [support_simulate', support_simulate_identity_oracle],
  ext x,
  simp only [set.mem_image, set.mem_set_of_eq,
    prod.exists, exists_and_distrib_right, exists_eq_right],
  refine ⟨λ h, h.rec_on (λ _ h, h), λ h, ⟨(), h⟩⟩,
end

end simulate'

end identity_oracle

section uniform_oracle

noncomputable def uniform_oracle (spec : oracle_spec) [spec.finite_range] : 
  simulation_oracle spec uniform_selecting :=
⟪ λ i t, $ᵗ (spec.range i) ⟫

@[simp]
lemma default_state_uniform_oracle (spec : oracle_spec) [spec.finite_range] :
  (uniform_oracle spec).default_state = () := rfl

@[simp]
lemma uniform_oracle_apply (spec : oracle_spec) (i : spec.ι) (t : spec.domain i) [spec.finite_range] (s : unit) :
  (uniform_oracle spec).o i (t, s) = $ᵗ (spec.range i) >>= λ u, return (u, ()) := rfl

end uniform_oracle
