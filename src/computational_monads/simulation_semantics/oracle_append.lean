/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.coercions.instances

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

section coe_append_right

/-- Coercing a computation on `spec` to one on `spec ++ spec'`, and then simulating with
two independent oracles `so ++ₛ so'` has the same support as simulating the original with `so`,
modulo the extra oracle state for the right oracle, which remains unchanged during simulation. -/
@[simp] lemma support_simulate_coe_append_right (s : S × S') (oa : oracle_comp spec α) :
  (simulate (so ++ₛ so') ↑oa s).support =
    (λ (x : α × S), (x.1, x.2, s.2)) '' (simulate so oa s.1).support :=
calc (simulate (so ++ₛ so') ↑oa s).support =
    (simulate (so ++ₛ so') ↑oa ((λ s₁, (s₁, s.2)) s.1)).support : by simp only [prod.mk.eta]
    ... = prod.map id (λ s₁, (s₁, s.2)) '' (simulate so oa s.1).support : begin
      refine (support_simulate_coe_sub_spec so (so ++ₛ so') s.1 oa _ (λ i t s, _)),
      simp_rw [is_sub_spec_append_right_apply, simulate_query, apply_inl_eq,
        support_bind_return, prod_map, id.def],
    end
    ... = (λ (x : α × S), (x.1, x.2, s.2)) '' (simulate so oa s.1).support : rfl

/-- Coercing a computation on `spec` to one on `spec ++ spec'`, and then simulating with
two independent oracles `so ++ₛ so'` has the same support as simulating the original with `so`,
if we use `simulate'` to ignore the final oracle state of the two `sim_oracle`s. -/
@[simp] lemma support_simulate'_coe_append_right (so : sim_oracle spec spec'' S)
  (so' : sim_oracle spec' spec'' S') (s : S × S') (oa : oracle_comp spec α) :
  (simulate' (so ++ₛ so') ↑oa s).support = (simulate' so oa s.1).support :=
set.ext (λ x, by simp only [support_simulate', support_simulate_coe_append_right, set.image_image])

end coe_append_right

section is_tracking

-- instance is_tracking [hso : so.is_tracking] [hso' : so'.is_tracking] :
--   (so ++ₛ so').is_tracking :=
-- {  }

-- @[simp] lemma answer_query_eq [so.is_tracking] [so'.is_tracking] :
--   (so ++ₛ so').answer_query = λ i, sum.rec_on i so.answer_query so'.answer_query := rfl

-- @[simp] lemma update_state_eq [so.is_tracking] [so'.is_tracking] :
--   (so ++ₛ so').update_state = λ s i, sum.rec_on i (λ i t u, (so.update_state s.1 i t u, s.2))
--     (λ i t u, (s.1, so'.update_state s.2 i t u)) := rfl

end is_tracking

section is_stateless

/-- Appending two stateless oracles together gives another stateless oracle. -/
instance is_stateless [hso : so.is_stateless] [hso' : so'.is_stateless] :
  (so ++ₛ so').is_stateless :=
{ state_subsingleton := @subsingleton.prod S S' hso.state_subsingleton hso'.state_subsingleton }

end is_stateless

end oracle_append

end sim_oracle