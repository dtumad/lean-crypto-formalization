import computational_monads.simulation_semantics.constructions.stateless_oracle

/-!
# Identity Oracle

Defines a `simulation_oracle` that just acts as an identity,
  e.g. simulation with this oracle has no effect (besides an empty state)

Main use cases is in simulating a pair of oracles, where only one of the oracles is reduced.
  For example preserving a `uniform_selecting` oracle while reducing a `signing_oracle`
-/

open oracle_comp oracle_spec

variables {α β : Type} {spec spec' spec'' : oracle_spec}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s : unit)

@[simps]
def identity_oracle (spec : oracle_spec) : simulation_oracle spec spec :=
⟪query⟫

-- TODO: should the notation take the `oracle_spec` as an arg?
notation `idₛ` := identity_oracle _

namespace identity_oracle

instance S_unique : unique (identity_oracle spec).S := punit.unique

@[simp]
lemma apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  (idₛ).o i (t, s) = query i t >>= λ u, return (u, ()) := rfl

section support

@[simp]
lemma support_apply (i : spec.ι) (t : spec.domain i) :
  ((idₛ).o i (t, s)).support = {u | u.1 ∈ (query i t).support} :=
begin
  simp only [apply, support_bind, support_pure, set.Union_true,
    set.Union_singleton_eq_range, support_query, set.top_eq_univ, set.mem_univ, set.set_of_true],
  exact set.eq_univ_of_forall (λ x, set.mem_range.2
    ⟨x.1, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, punit_eq () x.snd⟩⟩),
end

@[simp]
theorem support_simulate : (simulate idₛ oa s).support = {x | x.1 ∈ oa.support} :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { ext x,
    simp [prod.eq_iff_fst_eq_snd_eq, support_simulate_return,
      punit_eq x.snd (), punit_eq () s] },
  { ext x,    
    simp only [hoa, hob, unique.exists_iff, bind'_eq_bind, simulate_bind, support_bind,
      set.mem_set_of_eq, set.mem_Union, prod.exists] },
  { rw [simulate_query, support_apply] }
end

@[simp]
lemma mem_support_simulate_iff (x : α × unit) :
  x ∈ (simulate idₛ oa s).support ↔ x.1 ∈ oa.support :=
by simpa

@[simp]
lemma support_simulate' : (simulate' idₛ oa s).support = oa.support :=
begin
  ext x,
  simp only [support_simulate', support_simulate, set.mem_image, set.mem_set_of_eq,
    unique.exists_iff, prod.exists, exists_and_distrib_right, exists_eq_right],
end

end support

section distribution_semantics

open distribution_semantics

variable [spec.finite_range]

section equiv

@[simp]
lemma apply_equiv (i : spec.ι) (t : spec.domain i) :
  (idₛ).o i (t, s) ≃ₚ (λ u, (u, ())) <$> query i t :=
rfl

@[simp]
theorem simulate_equiv : simulate idₛ oa s ≃ₚ (λ a, (a, ())) <$> oa :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { simp [punit_eq s ()] },
  { exact trans (simulate_bind_equiv idₛ oa ob s) (trans (bind_equiv_of_equiv_of_equiv
      (hoa s) (λ x, hob x.fst x.snd)) (by simp)) },
  { exact (simulate_query_equiv idₛ i t ()).trans (apply_equiv () i t) }
end

lemma default_simulate_equiv : default_simulate idₛ oa ≃ₚ (λ a, (a, ())) <$> oa :=
simulate_equiv oa ()

@[simp]
lemma simulate'_equiv : (simulate' idₛ oa s) ≃ₚ oa :=
calc simulate' idₛ oa s ≃ₚ prod.fst <$> simulate idₛ oa s : rfl
  ... ≃ₚ prod.fst <$> (λ a, (a, ())) <$> oa : (map_equiv_of_equiv _ (simulate_equiv oa s))
  ... ≃ₚ (prod.fst ∘ λ a, (a, ())) <$> oa : map_map_equiv oa _ _
  ... ≃ₚ oa : map_id_equiv oa

lemma default_simulate'_equiv : default_simulate' idₛ oa ≃ₚ oa :=
simulate'_equiv oa ()

end equiv

section prob_event



end prob_event

end distribution_semantics

end identity_oracle