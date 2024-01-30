/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.instances
import computational_monads.simulation_semantics.is_tracking

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

namespace sim_oracle

def oracle_append (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S') :
  sim_oracle (spec ++ spec') spec'' (S × S') :=
λ i, match i with
| (sum.inl i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₁'⟩ ← so i (t, s₁), return (u, s₁', s₂)}
| (sum.inr i) := λ ⟨t, s₁, s₂⟩, do {⟨u, s₂'⟩ ← so' i (t, s₂), return (u, s₁, s₂')}
end

-- TODO: `++ₛₒ`??
infixl ` ++ₛ `:65 := oracle_append

namespace oracle_append

variables (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S')
  (oa : oracle_comp (spec ++ spec') α) (ob : α → oracle_comp (spec ++ spec') β) (a : α)
  (i : spec.ι) (i' : spec'.ι) (t : spec.domain i) (t' : spec'.domain i') (s : S × S')
  (x : spec.domain i × S × S') (x' : spec'.domain i' × S × S')

@[simp] lemma apply_inl_eq : (so ++ₛ so') (sum.inl i) x =
  do {u_s' ← so i (x.1, x.2.1), return (u_s'.1, u_s'.2, x.2.2)} :=
begin
  cases x with t s, cases s with s₁ s₂,
  refine congr_arg (λ ou, so i (t, s₁) >>= ou) (funext $ λ y, _),
  cases y, refl,
end

@[simp] lemma apply_inr_eq : (so ++ₛ so') (sum.inr i') x' =
  do {u_s' ← so' i' (x'.1, x'.2.2), return (u_s'.1, x'.2.1, u_s'.2)} :=
begin
  cases x' with t s, cases s with s₁ s₂,
  refine congr_arg (λ ou, so' i' (t, s₂) >>= ou) (funext $ λ y, _),
  cases y, refl,
end

section support

lemma support_apply_inl : ((so ++ₛ so') (sum.inl i) (t, s)).support =
  {x | (x.1, x.2.1) ∈ (so i (t, s.1)).support ∧ x.2.2 = s.2} :=
begin
  ext x,
  simp only [apply_inl_eq, support_bind, support_return, set.mem_Union,
    set.mem_singleton_iff, exists_prop, prod.exists, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨u, s', hu, hx⟩ := h,
    simpa only [hx, eq_self_iff_true, and_true] using hu },
  { refine ⟨x.1, x.2.1, _⟩,
    simp only [← h.2, h.1, true_and, prod.mk.eta] }
end

lemma support_apply_inr : ((so ++ₛ so') (sum.inr i') (t', s)).support =
  {x | (x.1, x.2.2) ∈ (so' i' (t', s.2)).support ∧ x.2.1 = s.1} :=
begin
  ext x,
  simp only [apply_inr_eq, support_bind, support_return, set.mem_Union,
    set.mem_singleton_iff, exists_prop, prod.exists, set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨u, s', hu, hx⟩ := h,
    simpa only [hx, eq_self_iff_true, and_true] using hu },
  { refine ⟨x.1, x.2.2, _⟩,
    simp only [← h.2, h.1, true_and, prod.mk.eta] }
end

end support

end oracle_append

section coercions

-- TODO: there are more coercions that should be added here
-- It may be possible to move these into the instances file itself even

variables variables (so : sim_oracle spec spec'' S) (so' : sim_oracle spec' spec'' S')

@[simp] lemma simulate_coe_append_right (s : S × S') (oa : oracle_comp spec α) :
  simulate (so ++ₛ so') ↑oa s = (λ (x : α × S), (x.1, x.2, s.2)) <$> simulate so oa s.1 :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { simp only [coe_sub_spec_return, simulate_return, map_pure, prod.mk.eta] },
  { simp [hoa, bind_assoc] }
end

@[simp] lemma simulate'_coe_append_right (s : S × S') (oa : oracle_comp spec α) :
  (simulate' (so ++ₛ so') ↑oa s) = simulate' so oa s.1 :=
by simp [simulate'.def]

@[simp] lemma simulate_coe_append_left (s : S × S') (oa : oracle_comp spec' α) :
  simulate (so ++ₛ so') ↑oa s = (λ (x : α × S'), (x.1, s.1, x.2)) <$> simulate so' oa s.2 :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s,
  { simp only [coe_sub_spec_return, simulate_return, map_pure, prod.mk.eta] },
  { simp [hoa, bind_assoc] }
end

@[simp] lemma simulate'_coe_append_left (s : S × S') (oa : oracle_comp spec' α) :
  (simulate' (so ++ₛ so') ↑oa s) = simulate' so' oa s.2 :=
by simp [simulate'.def]

end coercions

end sim_oracle