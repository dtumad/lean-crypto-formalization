import computational_monads.simulation_semantics.constructions.stateless_oracle

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}
  (oa : oracle_comp spec A)

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
  ⦃simulate idₛ oa s⦄ = (λ a, (a, ())) <$> ⦃oa⦄ :=
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