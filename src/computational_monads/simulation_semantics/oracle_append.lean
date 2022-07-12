import computational_monads.simulation_semantics.simulate

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}
  (a : A) (oa : oracle_comp (spec' ++ spec'') A)
  (ob : A → oracle_comp (spec' ++ spec'') B)

section oracle_append

def oracle_append (so : simulation_oracle spec spec'')
  (so' : simulation_oracle spec' spec'') :
  simulation_oracle (spec ++ spec') spec'' :=
{ S := so.S × so'.S,
  default_state := (so.default_state, so'.default_state),
  o := λ i, sum.rec_on i
    (λ i, λ x, do { u_s' ← so.o i ⟨x.1, x.2.1⟩, pure (u_s'.1, u_s'.2, x.2.2) })
    (λ i, λ x, do { u_s' ← so'.o i ⟨x.1, x.2.2⟩, pure (u_s'.1, x.2.1, u_s'.2) }) }

notation so `⟪++⟫` so' := oracle_append so so'

variables (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec'')
  (i : spec.ι) (i' : spec'.ι) (t : spec.domain i) (t' : spec'.domain i')
  (s : so.S × so'.S)

@[simp]
lemma default_state_oracle_append : (so ⟪++⟫ so').default_state =
  (so.default_state, so'.default_state) := rfl

lemma oracle_append_apply_index (i : spec.ι ⊕ spec'.ι) : (so ⟪++⟫ so').o i = sum.rec_on i
  (λ i, λ x, do { u_s' ← so.o i ⟨x.1, x.2.1⟩, pure (u_s'.1, u_s'.2, x.2.2) })
  (λ i, λ x, do { u_s' ← so'.o i ⟨x.1, x.2.2⟩, pure (u_s'.1, x.2.1, u_s'.2) }) := rfl

@[simp]
lemma oracle_append_apply_inl : (so ⟪++⟫ so').o (sum.inl i) (t, s) =
  do { u_s' ← so.o i ⟨t, s.1⟩, pure (u_s'.1, u_s'.2, s.2) } := rfl

@[simp]
lemma oracle_append_apply_inr : (so ⟪++⟫ so').o (sum.inr i') (t', s) =
  do { u_s' ← so'.o i' ⟨t', s.2⟩, pure (u_s'.1, s.1, u_s'.2)} := rfl

section simulate

variable [spec''.finite_range]

lemma simulate_oracle_append_pure : simulate (so ⟪++⟫ so') (pure a) s ≃ₚ
  (pure (a, s) : oracle_comp spec'' _) := rfl

end simulate

end oracle_append