/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.support

/-!
# Simulation with Subsingleton State

This file gives additional lemmas about `simulate` and `simulate'` when
the oracle's internal state is a `subsingleton` type.
In particular we can often relate simulations to `default_simulate` and `default_simulate'`.

`stateless_oracle` is the biggest example of this, as its internal state type is `unit`
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale nnreal ennreal

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
variables (a : α) (i : spec.ι) (t : spec.domain i)
  (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) (s : S) (s' : S') (f : α → β)

section support

/-- Reduce to the default state for oracles with a subsingleton state type -/
@[simp] lemma support_simulate_eq_support_default_simulate [subsingleton S] (s : S) :
  (simulate so oa s).support = (default_simulate so oa).support :=
subsingleton.elim so.default_state s ▸ rfl

/-- Reduce to the default state for oracles with a subsingleton state type -/
@[simp] lemma support_simulate'_eq_support_default_simulate' [subsingleton S] (s : S) :
  (simulate' so oa s).support = (default_simulate' so oa).support :=
subsingleton.elim so.default_state s ▸ rfl

/-- Version of `support_simulate'_eq_support` for `default_simulate`, given a `subsingleton` state.
Has a weaker requirement for the hypothesis `h` that the more general lemma -/
theorem support_simulate'_eq_support_of_subsingleton [subsingleton S] (s : S)
  (h : ∀ i t, prod.fst '' (so i (t, so.default_state)).support = ⊤) :
  (simulate' so oa s).support = oa.support :=
support_simulate'_eq_support so oa s (λ i t s, subsingleton.elim so.default_state s ▸ h i t)

/-- Given the state is `subsingleton`, the support of `simulate` is determined by `simulate'` -/
lemma support_simulate_eq_preimage_support_simulate' [subsingleton S] :
  (simulate so oa s).support = prod.fst ⁻¹' (default_simulate' so oa).support :=
begin
  sorry,
  -- have : (λ (x : α × S), (x.fst, so.default_state)) = id,
  -- from funext (λ x, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, subsingleton.elim _ x.2⟩),
  -- rw [support_simulate', set.image_image, this, set.image_id,
  --   support_simulate_eq_support_default_simulate],
end

/-- Given the state is `subsingleton`, membership in `support` of `simulate` can be checked
by just checking that the first component is in the support of `simulate'` -/
lemma mem_support_simulate_iff_fst_mem_support_simulate' (x : α × S) [subsingleton S] :
  x ∈ (simulate so oa s).support ↔ x.fst ∈ (simulate' so oa s).support :=
begin
  refine subsingleton.elim so.default_state s ▸ _,
  rw [support_simulate_eq_preimage_support_simulate', set.mem_preimage],
end

lemma support_simulate_eq_support_simulate_of_subsingleton [subsingleton S] (so : sim_oracle spec spec' S)
  (so' : sim_oracle spec spec'' S) (s s' : S)
  (h : ∀ i t, prod.fst '' (so i (t, so.default_state)).support =
    prod.fst '' (so' i (t, so'.default_state)).support) :
  (simulate so oa s).support = (simulate so' oa s').support :=
begin
  simp only [support_simulate_eq_preimage_support_simulate'],
  refine congr_arg _ _,
  refine support_simulate'_eq_support_simulate' _ oa _ _,
  intros i t s s',
  rw [subsingleton.elim s so.default_state, subsingleton.elim s' so'.default_state],
  refine h i t,
end

end support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

@[simp]
lemma eval_dist_simulate_eq_eval_dist_default_simulate [subsingleton S] (s : S) :
  ⦃simulate so oa s⦄ = ⦃default_simulate so oa⦄ := subsingleton.elim so.default_state s ▸ rfl

lemma eval_dist_simulate'_eq_eval_dist_default_simulate' [subsingleton S] (s : S) :
  ⦃simulate' so oa s⦄ = ⦃default_simulate' so oa⦄ := subsingleton.elim so.default_state s ▸ rfl

end eval_dist

section prob_event

end prob_event

end distribution_semantics

end oracle_comp