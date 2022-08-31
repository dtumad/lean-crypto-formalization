import computational_monads.simulation_semantics.default_simulate

open oracle_comp oracle_spec

variables {spec spec' spec'' spec''' : oracle_spec} {A B C : Type} {α β γ : Type}
  (a : A) (oa : oracle_comp (spec' ++ spec'') A)
  (ob : A → oracle_comp (spec' ++ spec'') B)

section oracle_append

-- def oracle_append' (so : simulation_oracle spec spec'')
--   (so' : simulation_oracle spec' spec''') :
--   simulation_oracle (spec ++ spec') (spec'' ++ spec''') :=
-- {
--   S := so.S × so'.S,
--   default_state := (so.default_state, so'.default_state),
--   o := sorry
-- }

-- notation so `+++ₛ` so' := oracle_append' so so'

-- TODO: `simulation_oracle.append`
def oracle_append (so : simulation_oracle spec spec'')
  (so' : simulation_oracle spec' spec'') :
  simulation_oracle (spec ++ spec') spec'' :=
{ S := so.S × so'.S,
  default_state := (so.default_state, so'.default_state),
  o := λ i, sum.rec_on i
    (λ i, λ x, do { u_s' ← so.o i ⟨x.1, x.2.1⟩, pure (u_s'.1, u_s'.2, x.2.2) })
    (λ i, λ x, do { u_s' ← so'.o i ⟨x.1, x.2.2⟩, pure (u_s'.1, x.2.1, u_s'.2) }) }

-- TODO: should be infix?
notation so `++ₛ` so' := oracle_append so so'

-- -- Reduce some of the appended oracles independently, and others into a single
-- example (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec')
--   (so'' : simulation_oracle spec'' spec''') :
--   simulation_oracle ((spec ++ spec') ++ spec'') (spec' ++ spec''') :=
-- (so ++ₛ so') +++ₛ so''

variables (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec'')
  (i : spec.ι) (i' : spec'.ι) (t : spec.domain i) (t' : spec'.domain i')
  (s : so.S × so'.S)

@[simp]
lemma default_state_oracle_append : (so ++ₛ so').default_state =
  (so.default_state, so'.default_state) := rfl

lemma oracle_append_apply_index (i : spec.ι ⊕ spec'.ι) : (so ++ₛ so').o i = sum.rec_on i
  (λ i, λ x, do { u_s' ← so.o i ⟨x.1, x.2.1⟩, pure (u_s'.1, u_s'.2, x.2.2) })
  (λ i, λ x, do { u_s' ← so'.o i ⟨x.1, x.2.2⟩, pure (u_s'.1, x.2.1, u_s'.2) }) := rfl

@[simp]
lemma oracle_append_apply_inl : (so ++ₛ so').o (sum.inl i) (t, s) =
  do { u_s' ← so.o i (t, s.1), pure (u_s'.1, u_s'.2, s.2) } := rfl

@[simp]
lemma oracle_append_apply_inr : (so ++ₛ so').o (sum.inr i') (t', s) =
  do { u_s' ← so'.o i' (t', s.2), pure (u_s'.1, s.1, u_s'.2)} := rfl

section support

lemma support_oracle_append_apply_inl : ((so ++ₛ so').o (sum.inl i) (t, s)).support =
  {x | (x.1, x.2.1) ∈ (so.o i (t, s.1)).support ∧ x.2.2 = s.2} :=
begin
  ext x,
  simp only [oracle_append_apply_inl, support_bind, support_pure, set.mem_Union,
    set.mem_singleton_iff, exists_prop, prod.exists, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨u, s', hu, hx⟩ := h,
    simpa only [hx, eq_self_iff_true, and_true] using hu },
  { refine ⟨x.1, x.2.1, _⟩,
    simp only [← h.2, h.1, true_and, prod.mk.eta] }
end

lemma support_oracle_append_apply_inr : ((so ++ₛ so').o (sum.inr i') (t', s)).support =
  {x | (x.1, x.2.2) ∈ (so'.o i' (t', s.2)).support ∧ x.2.1 = s.1} :=
begin
  ext x,
  simp only [oracle_append_apply_inr, support_bind, support_pure, set.mem_Union,
    set.mem_singleton_iff, exists_prop, prod.exists, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨u, s', hu, hx⟩ := h,
    simpa only [hx, eq_self_iff_true, and_true] using hu },
  { refine ⟨x.1, x.2.2, _⟩,
    simp only [← h.2, h.1, true_and, prod.mk.eta] }
end

-- GOALS:
-- simulate' prop holds on both oracles -> holds on appended oracle
-- state prop holds on first oracles -> holds for first state value
-- state prop holds on second oracle -> holds for second state value

lemma spec_thing (e : set A) (oa : oracle_comp (spec ++ spec') A) (s : so.S × so'.S)
  (hp : ∀ (oa : oracle_comp spec A) s, (simulate' so oa s).support ⊆ e)
  (hq : ∀ (oa : oracle_comp spec' A) s, (simulate' so' oa s).support ⊆ e) :
  (simulate' (so ++ₛ so') oa s).support ⊆ e :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  { simpa only [pure'_eq_pure, support_simulate'_pure] using hp (pure a) s.1 },
  {
    sorry,
  },
  {
    -- rw [support_simulate'_query],
    induction i with i i,
    {
      specialize hp (query i t) s.1,
      rw [support_simulate'_query] at ⊢ hp,
      rw [support_oracle_append_apply_inl],
      refine trans _ hp,
      refine λ u hu, _,
      simp at hu ⊢,
      obtain ⟨⟨s, s'⟩, hu⟩ := hu,
      refine ⟨s, hu.1⟩,
    },
    sorry
  }
end

end support



-- TODO: organize
section simulate

lemma simulate_oracle_append_pure : simulate (so ++ₛ so') (pure a) s = (pure (a, s)) := rfl

end simulate

section simulate'

section distribution_semantics

variable [spec''.finite_range]

lemma simulate'_oracle_append_pure_equiv : simulate' (so ++ₛ so') (pure a) s ≃ₚ
  (pure a : oracle_comp spec'' _) := by simp

end distribution_semantics

end simulate'

section default_simulate

lemma default_simulate_oracle_append_pure : default_simulate (so ++ₛ so') (pure a) =
  (pure (a, (so.default_state, so'.default_state))) := rfl

end default_simulate

section default_simulate'

section distribution_semantics

variable [spec''.finite_range]

lemma default_simulate'_oracle_append_pure_equiv : default_simulate' (so ++ₛ so') (pure a) ≃ₚ
  (pure a : oracle_comp spec'' _) := by simp

end distribution_semantics

end default_simulate'

end oracle_append