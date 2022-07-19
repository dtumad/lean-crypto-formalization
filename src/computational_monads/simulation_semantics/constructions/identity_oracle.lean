import computational_monads.simulation_semantics.constructions.stateless_oracle

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}

@[simps]
def identity_oracle (spec : oracle_spec) : simulation_oracle spec spec :=
⟪ query ⟫

notation `idₛ` := identity_oracle _

namespace identity_oracle

section instances

instance S_unique : unique (identity_oracle spec).S :=
punit.unique

end instances

@[simp]
lemma apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  (identity_oracle spec).o i (t, s) = query i t >>= λ u, return (u, ()) := rfl

section support

@[simp]
lemma support_apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  ((identity_oracle spec).o i (t, s)).support = { u | u.1 ∈ (query i t).support } :=
begin
  simp only [apply, support_bind, support_pure, set.Union_true,
    set.Union_singleton_eq_range, support_query, set.top_eq_univ, set.mem_univ, set.set_of_true],
  exact set.eq_univ_of_forall (λ x, set.mem_range.2
    ⟨x.1, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, punit_eq () x.snd⟩⟩),
end

@[simp]
theorem support_simulate (oa : oracle_comp spec A) (s : unit) :
  (simulate idₛ oa s).support = {x | x.1 ∈ oa.support} :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { ext x,
    simp [prod.eq_iff_fst_eq_snd_eq, punit_eq x.snd (), punit_eq () s] },
  { ext x,    
    simp only [hoa, hob, unique.exists_iff, bind'_eq_bind, simulate_bind, support_bind, set.mem_set_of_eq, set.mem_Union,
      prod.exists] },
  { rw [simulate_query, support_apply] }
end

@[simp]
lemma mem_support_simulate_iff (oa : oracle_comp spec A) (s : unit) (x : A × unit) :
  x ∈ (simulate idₛ oa s).support ↔ x.1 ∈ oa.support :=
by simpa

@[simp]
lemma support_simulate' (oa : oracle_comp spec A) (s : unit) :
  (simulate' idₛ oa s).support = oa.support :=
begin
  ext x,
  simp only [support_simulate', support_simulate, set.mem_image, set.mem_set_of_eq,
    unique.exists_iff, prod.exists, exists_and_distrib_right, exists_eq_right],
end

end support

section equiv

open distribution_semantics

variable [spec.finite_range]

@[simp]
lemma apply_equiv (i : spec.ι) (t : spec.domain i) (s : unit) :
  (identity_oracle spec).o i (t, s) ≃ₚ (λ u, (u, ())) <$> query i t :=
rfl

@[simp]
theorem simulate_equiv (oa : oracle_comp spec A) (s : unit) :
  simulate idₛ oa s ≃ₚ (λ a, (a, ())) <$> oa :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { simp [punit_eq s ()] },
  { exact trans (simulate_bind_equiv idₛ oa ob s) (trans (bind_equiv_of_equiv_of_equiv
      (hoa s) (λ x, hob x.fst x.snd)) (by simp)) },
  { exact (simulate_query_equiv idₛ i t ()).trans (apply_equiv i t ()) }
end

lemma default_simulate_equiv (oa : oracle_comp spec A) (s : unit) :
  default_simulate idₛ oa ≃ₚ (λ a, (a, ())) <$> oa :=
simulate_equiv oa ()

@[simp]
lemma simulate'_identity_oracle_equiv (oa : oracle_comp spec A) (s : unit) :
  (simulate' idₛ oa s) ≃ₚ oa :=
calc simulate' idₛ oa s ≃ₚ prod.fst <$> simulate idₛ oa s : rfl
  ... ≃ₚ prod.fst <$> (λ a, (a, ())) <$> oa : (map_equiv_of_equiv _ (simulate_equiv oa s))
  ... ≃ₚ (prod.fst ∘ λ a, (a, ())) <$> oa : map_map_equiv oa _ _
  ... ≃ₚ oa : map_equiv_of_eq_id _ _ (by simp)

lemma default_simulate'_equiv (oa : oracle_comp spec A) (s : unit) :
  default_simulate' idₛ oa ≃ₚ oa :=
simulate'_identity_oracle_equiv oa ()

end equiv

section prob_event



end prob_event



end identity_oracle