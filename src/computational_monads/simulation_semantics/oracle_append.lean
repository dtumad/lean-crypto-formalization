import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.constructions.stateless_oracle

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
  o := λ i, match i with
  | sum.inl i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so.o i ⟨t, s.1⟩, pure (u, s', s.2) }
  | sum.inr i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so'.o i ⟨t, s.2⟩, pure (u, s.1, s') }
  end }

notation so `⟪++⟫` so' := oracle_append so so'

variables (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec'')
  (i : spec.ι) (i' : spec'.ι) (t : spec.domain i) (t' : spec'.domain i')
  (s : so.S × so'.S)

@[simp]
lemma default_state_oracle_append : (so ⟪++⟫ so').default_state =
  (so.default_state, so'.default_state) := rfl

@[simp]
lemma oracle_append_apply_inl : (so ⟪++⟫ so').o (sum.inl i) (t, s) =
  so.o i (t, s.1) >>= λ ⟨u, s'⟩, pure (u, s', s.2) :=
begin
  simp [oracle_append],
  sorry
end

-- @[simp]
-- lemma simulate_oracle_append_pure : simulate (so ⟪++⟫ so') (pure a) s ≃ₚ

end oracle_append