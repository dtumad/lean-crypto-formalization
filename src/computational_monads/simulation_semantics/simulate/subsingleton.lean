/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.simulate'_idem

/-!
# Simulation with Subsingleton State

This file gives additional lemmas about `simulate` and `simulate'` when
the oracle's internal state is a `subsingleton` type.
In particular we can often relate simulations to `default_simulate` and `default_simulate'`.

These lemmas are mainly used to prove things about `sim_oracle`s with a `is_stateless` instance,
which essentially just bundles in the statelessness of the state type.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale nnreal ennreal

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
variables (a : α) (i : spec.ι) (t : spec.domain i)
  (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) (s : S) (s' : S') (f : α → β)

lemma simulate_eq_default_simulate [subsingleton S] :
  simulate so oa s = default_simulate so oa := subsingleton.elim so.default_state s ▸ rfl

lemma simulate'_eq_default_simulate' [subsingleton S] :
  simulate' so oa s = default_simulate' so oa := subsingleton.elim so.default_state s ▸ rfl

section support

/-- Version of `support_simulate'_eq_support` for `default_simulate`, given a `subsingleton` state.
Has a weaker requirement for the hypothesis `h` than the more general lemma -/
lemma support_simulate'_eq_support_of_subsingleton [subsingleton S] (s : S)
  (h : ∀ i t, prod.fst '' (so i (t, so.default_state)).support = ⊤) :
  (simulate' so oa s).support = oa.support :=
support_simulate'_eq_support oa s (λ i t s, subsingleton.elim so.default_state s ▸ h i t)

/-- Given the state is `subsingleton`, the support of `simulate` is determined by `simulate'` -/
lemma support_simulate_eq_preimage_support_simulate' [subsingleton S] :
  (simulate so oa s).support = prod.fst ⁻¹' (default_simulate' so oa).support :=
begin
  rw [support_simulate', subsingleton.elim so.default_state s],
  exact (set.ext $ λ x, ⟨λ h, ⟨x, h, rfl⟩, λ h, let ⟨y, h, h'⟩ := h in
    (prod.eq_iff_fst_eq_snd_eq.2 ⟨h', subsingleton.elim y.2 x.2⟩) ▸ h⟩),
end

/-- If the state has at most one elements, we can express the support of `simulate` in terms
of only `simulate'`. For example in a `stateless_oracle` or `uniformₛₒ`.
TODO: above is basically the same statement -/
lemma support_simulate_eq_support_simulate'_of_subsingleton [subsingleton S]
  (so : sim_oracle spec spec' S) : (simulate so oa s).support =
    {x | x.1 ∈ (simulate' so oa s).support} :=
begin
  refine set.ext (λ x, _),
  rw [set.mem_set_of, support_simulate', set.mem_image],
  refine ⟨λ h, ⟨x, h, rfl⟩, λ h, _⟩,
  obtain ⟨y, hy, h⟩ := h,
  rwa [← @prod.mk.eta _ _ x, ← h, subsingleton.elim x.2 y.2, prod.mk.eta],
end

/-- Given the state is `subsingleton`, membership in `support` of `simulate` can be checked
by just checking that the first component is in the support of `simulate'` -/
lemma mem_support_simulate_iff_fst_mem_support_simulate' (x : α × S) [subsingleton S] :
  x ∈ (simulate so oa s).support ↔ x.fst ∈ (simulate' so oa s).support :=
begin
  refine subsingleton.elim so.default_state s ▸ _,
  rw [support_simulate_eq_preimage_support_simulate', set.mem_preimage],
end

lemma support_simulate_eq_support_simulate_of_subsingleton [subsingleton S]
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S) (s s' : S)
  (h : ∀ i t, prod.fst '' (so i (t, so.default_state)).support =
    prod.fst '' (so' i (t, so'.default_state)).support) :
  (simulate so oa s).support = (simulate so' oa s').support :=
begin
  simp only [support_simulate_eq_preimage_support_simulate'],
  refine congr_arg _ (support_simulate'_eq_support_simulate' oa _ _ _),
  intros i t s s',
  rw [subsingleton.elim s so.default_state, subsingleton.elim s' so'.default_state, h i t],
end

end support

section eval_dist

lemma eval_dist_simulate_eq_map_eval_dist_simulate'_of_subsingleton [subsingleton S] (s : S) :
  ⁅simulate so oa s⁆ = ⁅simulate' so oa s⁆.map (λ x, (x, s)) :=
begin
  have : (λ (x : α), (x, s)) ∘ prod.fst = id,
  from funext (λ x, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, subsingleton.elim _ _⟩),
  rw [eval_dist_simulate', pmf.map_comp, this, pmf.map_id],
end

lemma prob_output_simulate_eq_prob_output_simulate'_of_subsingleton [subsingleton S]
  (s : S) (x : α × S) : ⁅= x | simulate so oa s⁆ = ⁅= x.1 | simulate' so oa s⁆ :=
begin
  simp only [prob_output.def, eval_dist_simulate_eq_map_eval_dist_simulate'_of_subsingleton],
  refine trans (tsum_eq_single x.1 $ λ y hy, by simp [prod.eq_iff_fst_eq_snd_eq, hy.symm])
    (by simp [prod.eq_iff_fst_eq_snd_eq]),
end

lemma simulate_dist_equiv_of_subsingleton [subsingleton S]
  (s : S) : simulate so oa s ≃ₚ (λ x, (x, s)) <$> simulate' so oa s :=
begin
  rw_dist_equiv [map_comp_dist_equiv],
  refine trans (map_id_dist_equiv _).symm (map_dist_equiv_of_dist_equiv' (funext (λ x, _)) rfl),
  simp [prod.eq_iff_fst_eq_snd_eq],
end

end eval_dist

section prob_event

lemma prob_event_simulate_eq_prob_event_image_simulate_of_subsingleton [subsingleton S] (s : S)
  (e : set (α × S)) : ⁅e | simulate so oa s⁆ = ⁅prod.fst '' e | simulate' so oa s⁆ :=
begin
  refine trans ((simulate_dist_equiv_of_subsingleton _ _ _).prob_event_eq e) _,
  rw [prob_event_map],
  refine congr_arg (λ e, ⁅e | simulate' so oa s⁆) (set.ext (λ x, _)),
  simp only [set.mem_preimage, set.mem_image, prod.exists, exists_and_distrib_right,
    exists_eq_right],
  refine ⟨λ h, ⟨s, h⟩, λ h, let ⟨s', hs'⟩ := h in (subsingleton.elim s' s) ▸ hs'⟩,
end

end prob_event

end oracle_comp