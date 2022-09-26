import computational_monads.simulation_semantics.default_simulate

open oracle_comp oracle_spec

variables {spec spec' spec'' spec''' : oracle_spec} {A B C : Type} {α β γ : Type}
  
namespace simulation_oracle

def oracle_append (so : simulation_oracle spec spec'')
  (so' : simulation_oracle spec' spec'') :
  simulation_oracle (spec ++ spec') spec'' :=
{ S := so.S × so'.S,
  default_state := (so.default_state, so'.default_state),
  o := λ i, match i with
  | (sum.inl i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₁'⟩ ← so i (t, s₁), return (u, s₁', s₂)}
  | (sum.inr i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₂'⟩ ← so' i (t, s₂), return (u, s₁, s₂')}
  end }
  
-- TODO: should be infix?
notation so `++ₛ` so' := oracle_append so so'

-- TODO: namespace
@[inline, reducible]
def oracle_append.mk_S {so : simulation_oracle spec spec''} {so' : simulation_oracle spec' spec''}
  (s : so.S) (s' : so'.S) : (so ++ₛ so').S := (s, s')

variables (so : simulation_oracle spec spec'') (so' : simulation_oracle spec' spec'')
  (oa : oracle_comp (spec ++ spec') A) (ob : A → oracle_comp (spec ++ spec') B) (a : A)
  (i : spec.ι) (i' : spec'.ι) (t : spec.domain i) (t' : spec'.domain i') (s : so.S × so'.S)
  (x : spec.domain i × so.S × so'.S) (x' : spec'.domain i' × so.S × so'.S)

@[simp]
lemma default_state_oracle_append : (so ++ₛ so').default_state =
  (so.default_state, so'.default_state) := rfl

@[simp]
lemma oracle_append_apply_inl : (so ++ₛ so') (sum.inl i) x =
  do {u_s' ← so i (x.1, x.2.1), return (u_s'.1, u_s'.2, x.2.2)} :=
begin
  cases x with t s, cases s with s₁ s₂,
  refine congr_arg (λ ou, so i (t, s₁) >>= ou) (funext $ λ y, _),
  cases y, refl,
end

@[simp]
lemma oracle_append_apply_inr : (so ++ₛ so') (sum.inr i') x' =
  do {u_s' ← so' i' (x'.1, x'.2.2), return (u_s'.1, x'.2.1, u_s'.2)} :=
begin
  cases x' with t s, cases s with s₁ s₂,
  refine congr_arg (λ ou, so' i' (t, s₂) >>= ou) (funext $ λ y, _),
  cases y, refl,
end

section support

lemma support_oracle_append_apply_inl : ((so ++ₛ so') (sum.inl i) (t, s)).support =
  {x | (x.1, x.2.1) ∈ (so i (t, s.1)).support ∧ x.2.2 = s.2} :=
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

lemma support_oracle_append_apply_inr : ((so ++ₛ so') (sum.inr i') (t', s)).support =
  {x | (x.1, x.2.2) ∈ (so' i' (t', s.2)).support ∧ x.2.1 = s.1} :=
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
-- ??? simulate prop holds on both oracles -> holds on appended oracle
-- state prop holds on first oracles -> holds for first state value
-- state prop holds on second oracle -> holds for second state value

end support

section fin_support

end fin_support

-- TODO: organize
section distribution_semantics

open distribution_semantics

variable [spec''.finite_range]

section eval_dist

end eval_dist

section equiv

end equiv

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end simulation_oracle