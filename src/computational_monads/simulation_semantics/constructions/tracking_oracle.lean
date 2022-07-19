import computational_monads.simulation_semantics.default_simulate

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}

/-- Oracle where the query result is indepenent of the current oracle state,
  although the new state may depend upon the previous state.
  For example a logging oracle that just tracks the input and output of queries. -/
@[simps]
def tracking_oracle {spec : oracle_spec} {S : Type} (default_state : S)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S) :
  simulation_oracle spec spec' :=
{ S := S,
  default_state := default_state,
  o := λ i ⟨t, s⟩, do { u ← o i t, pure (u, update_state s i t u) } }

notation `⟪` o `|` update_state `,` default_state `⟫` :=
  tracking_oracle default_state o update_state

namespace tracking_oracle

variables (oa : oracle_comp spec A)

variables {S : Type} 
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state update_state' : Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state default_state' : S)

lemma apply (i : spec.ι) (t : spec.domain i) (s : S) :
  ⟪o | update_state, default_state⟫.o i (t, s) =
    do { u ← o i t, pure (u, update_state s i t u) } := rfl

section support

@[simp]
lemma support_apply (i : spec.ι) (t : spec.domain i) (s : S) :
  ((⟪o | update_state, default_state⟫).o i (t, s)).support
    = { u | u.1 ∈ (o i t).support ∧ u.2 = update_state s i t u.1 } :=
begin
  ext x,
  simp only [apply, support_bind, support_pure, set.mem_Union,
    set.mem_singleton_iff, exists_prop, set.mem_set_of_eq, prod.eq_iff_fst_eq_snd_eq],
  refine ⟨λ h, let ⟨x₁, h, h'⟩ := h in h'.1.symm ▸ ⟨h, h'.2⟩, λ h, ⟨x.1, ⟨h.1, rfl, h.2⟩⟩⟩,
end

/-- The first output is independent of any of the tracking state -/
lemma support_simulate'_eq_of_eq (oa : oracle_comp spec A) (s : S) :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support =
    (simulate' ⟪o | update_state', default_state'⟫ oa s).support :=
begin
  induction oa using oracle_comp.induction_on with a A A B oa ob hoa hob i t generalizing s,
  { simp },
  {
    ext x,
    simp only [support_simulate'_bind],
    simp [support_simulate'_bind, hoa, hob],
    refine ⟨λ h, _, λ h, _⟩,
    {
      obtain ⟨s, a, s', ⟨has, hx⟩⟩ := h,
      sorry,
    },
    {
      sorry,
    }
  },
  sorry,
end

end support

section simulate


end simulate

section eval_distribution

open distribution_semantics

variable [spec.finite_range]

-- TODO: should be able to find some generalization for lemmas looking like this
lemma simulate'_query_equiv_self (s : S) :
  simulate' (⟪query | update_state, default_state⟫) oa s ≃ₚ oa :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { simp only [pure'_eq_pure, simulate'_pure, map_pure_equiv, eval_distribution_return] },
  { let so := ⟪query | update_state, default_state⟫,
    calc simulate' so (oa >>= ob) s
      ≃ₚ simulate so oa s >>= λ x, simulate' so (ob x.1) x.2 : simulate'_bind_equiv _ oa ob _
      ... ≃ₚ simulate so oa s >>= λ x, (ob x.1) : bind_equiv_of_equiv_second _ (by simp [hob])
      ... ≃ₚ simulate' so oa s >>= ob : symm (bind_map_equiv _ prod.fst ob)
      ... ≃ₚ oa >>= ob : bind_equiv_of_equiv_first ob (hoa _) },
  { erw [simulate'_query_equiv, tracking_oracle_o,
      fst_map_bind_mk_equiv, map_id_equiv (query i t)], } 
end

end eval_distribution

end tracking_oracle