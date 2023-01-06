/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.sub_spec

/-!
# Appending Simulation Oracles

This file defines an append operation `++ₛ` for simulation oracles,
creating a simulation oracle for a combined set of initial oracles.
In particular, if simulation oracles `so` and `so'` have starting oracles given by
`spec` and `spec'`, then `so ++ₛ so'` will have starting oracles `spec ++ spec'`.

The implementation just maintains a seperate state for each oracle,
using pattern matching on queries to decide which `sim_oracle` to call.
-/

open oracle_comp oracle_spec

variables {spec spec' spec'' spec''' : oracle_spec} {α β γ : Type} {S S' : Type}

namespace sim_oracle -- TODO: `oracle_append` namespace?

def oracle_append (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S') :
  sim_oracle (spec ++ spec') spec'' (S × S') :=
{ default_state := (so.default_state, so'.default_state),
  o := λ i, match i with
  | (sum.inl i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₁'⟩ ← so i (t, s₁), return (u, s₁', s₂)}
  | (sum.inr i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₂'⟩ ← so' i (t, s₂), return (u, s₁, s₂')}
  end }

infixl ` ++ₛ `:65 := oracle_append

variables (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S')
  (oa : oracle_comp (spec ++ spec') α) (ob : α → oracle_comp (spec ++ spec') β) (a : α)
  (i : spec.ι) (i' : spec'.ι) (t : spec.domain i) (t' : spec'.domain i') (s : S × S')
  (x : spec.domain i × S × S') (x' : spec'.domain i' × S × S')

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
  simp only [oracle_append_apply_inl, support_bind, support_return, set.mem_Union,
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
  simp only [oracle_append_apply_inr, support_bind, support_return, set.mem_Union,
    set.mem_singleton_iff, exists_prop, prod.exists, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨u, s', hu, hx⟩ := h,
    simpa only [hx, eq_self_iff_true, and_true] using hu },
  { refine ⟨x.1, x.2.2, _⟩,
    simp only [← h.2, h.1, true_and, prod.mk.eta] }
end


-- NOTE: also useful, for ∘ₛ
lemma support_simulate'_simulate'_eq_support_simulate' {spec spec' spec'' : oracle_spec}
  {S S' S'' : Type} (so : sim_oracle spec spec' S) (so' : sim_oracle spec' spec'' S')
  (so'' : sim_oracle spec spec'' S'') (s : S) (s' : S') (s'' : S'')
  (oa : oracle_comp spec α) :
  (simulate' so' (simulate' so oa s) s').support = (simulate' so'' oa s'').support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  sorry,
  sorry,
  sorry
end

@[simp] lemma support_simulate_coe_append_right (so : sim_oracle spec spec'' S)
  (so' : sim_oracle spec' spec'' S') (s : S × S') (oa : oracle_comp spec α) :
  (simulate (so ++ₛ so') ↑oa s).support =
    {x | (x.1, x.2.1) ∈ (simulate so oa s.1).support ∧ x.2.2 = s.2} :=
calc (simulate (so ++ₛ so') ↑oa s).support =
  (simulate (so ++ₛ so') ↑oa ((λ s₁, (s₁, s.2)) s.1)).support :
    by simp only [prod.mk.eta]
  ... = prod.map id (λ x, (x, s.2)) '' (simulate so oa s.1).support :
    begin
      refine support_simulate_coe_sub_spec _ _ _ so (so ++ₛ so') _ _ _ (λ i t s, _),
      simp only [is_sub_spec_append_right_apply, simulate_query, oracle_append_apply_inl,
        support_bind_return, prod.map, id.def],
    end
  ... = {x | (x.1, x.2.1) ∈ (simulate so oa s.1).support ∧ x.2.2 = s.2} :
    begin
      ext x,
      simp only [set.mem_set_of, set.mem_image, prod.eq_iff_fst_eq_snd_eq,
        prod_map, id.def, prod.exists],
      refine ⟨λ h, let ⟨a, s₁, h, ha, hs₁, hs⟩ := h in ⟨ha ▸ hs₁ ▸ h, hs.symm⟩,
        λ h, ⟨x.1, x.2.1, h.1, rfl, rfl, h.2.symm⟩⟩,
    end

-- GOALS:
-- ??? simulate prop holds on both oracles -> holds on appended oracle
-- state prop holds on first oracles -> holds for first state value
-- state prop holds on second oracle -> holds for second state value

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

section eval_dist

end eval_dist

section prob_event

end prob_event

section indep_events

end indep_events

section indep_event

end indep_event

end distribution_semantics

end sim_oracle