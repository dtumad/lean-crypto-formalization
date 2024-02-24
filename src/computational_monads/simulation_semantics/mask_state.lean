/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_tracking

/-!
# State Masking for Simulation Oracles

This file defines a construction for masking the state of an oracle using some equivalence.
This is particularlly useful when combining multiple oracles,
as this can lead to irrelevent extra bits of the state floating around.
The definition is in terms of an equivalence `S ≃ S'` between types (i.e. a bijection),
with `S` the original state and `S'` the new one.

We also give the natural lemmas for the compatibility of masking with `support` and `eval_dist`,
showing that the masking doesn't affect their values (up to applying the mask to the state).
-/

variables {α β γ : Type} {spec spec' : oracle_spec} {S S' S'' : Type}

open oracle_comp oracle_spec equiv

namespace sim_oracle

/-- Mask the state value of an oracle, without changing the oracle's behaviour.
We capture this unchanged functionality by using an equivalence for the masking.
Convenient when working with composed or appended oracles, to remove unneeded state elements.
In particular `unit` state values that start spreading can be avoided. -/
def mask_state (so : sim_oracle spec spec' S) (mask : S ≃ S') :
  sim_oracle spec spec' S' :=
λ i x, prod.map id mask <$> (so i (prod.map id mask.symm x))

namespace mask_state

variables (so : sim_oracle spec spec' S) (mask : S ≃ S')

section simulate

variables (oa : oracle_comp spec α) (s' : S')

@[simp] lemma apply_eq {i : spec.ι} (z : spec.domain i × S') : so.mask_state mask i z =
  prod.map id mask <$> (so i (prod.map id mask.symm z)) := rfl

@[simp] lemma simulate_eq_map_simulate : simulate (so.mask_state mask) oa s' =
  (prod.map id mask) <$> simulate so oa (mask.symm s') :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing s',
  { simp only [simulate_return, map_pure, prod.map_mk, id.def, apply_symm_apply] },
  { simp [simulate_bind, simulate_query, oracle_comp.bind_map, function.comp, hoa] }
end

/-- Simulating with an oracle after masking the state is equivalent to simulating with the original
up to mapping the state values by the equivalence used in the masking. -/
lemma simulate_dist_equiv_map_simulate : simulate (so.mask_state mask) oa s' ≃ₚ
  (prod.map id mask) <$> simulate so oa (mask.symm s') :=
dist_equiv_of_eq (simulate_eq_map_simulate so mask oa s')

lemma support_simulate_eq_image_support_simulate :
  (simulate (so.mask_state mask) oa s').support =
    (prod.map id mask) '' (simulate so oa (mask.symm s')).support :=
trans (simulate_dist_equiv_map_simulate so mask oa s').support_eq (support_map _ _)

@[simp] lemma support_simulate_eq_preimage_support_simulate :
  (simulate (so.mask_state mask) oa s').support =
    (prod.map id mask.symm) ⁻¹' (simulate so oa (mask.symm s')).support :=
by rw [support_simulate_eq_image_support_simulate, set.image_eq_preimage_of_inverse];
  exact λ z, by simp only [prod_map, id.def, symm_apply_apply, apply_symm_apply, prod.mk.eta]

lemma fin_support_simulate_eq_image_support_simulate
  [decidable_eq α] [decidable_eq S] [decidable_eq S'] :
  (simulate (so.mask_state mask) oa s').fin_support =
    (simulate so oa (mask.symm s')).fin_support.image (prod.map id mask) :=
trans (simulate_dist_equiv_map_simulate so mask oa s').fin_support_eq (fin_support_map _ _)

@[simp] lemma fin_support_simulate_eq_preimage_fin_support_simulate
  [decidable_eq α] [decidable_eq S] [decidable_eq S'] :
  (simulate (so.mask_state mask) oa s').fin_support =
    (simulate so oa (mask.symm s')).fin_support.preimage (prod.map id mask.symm) (λ z hz z' hz' h,
    by simpa only [prod.eq_iff_fst_eq_snd_eq, prod_map, embedding_like.apply_eq_iff_eq] using h) :=
by simp only [fin_support_eq_iff_support_eq_coe, support_simulate_eq_preimage_support_simulate,
  finset.coe_preimage, coe_fin_support]

lemma eval_dist_simulate_eq_map_support_simulate :
  ⁅simulate (so.mask_state mask) oa s'⁆ =
    ⁅simulate so oa (mask.symm s')⁆.map (prod.map id mask) :=
trans (simulate_dist_equiv_map_simulate so mask oa s').eval_dist_eq (eval_dist_map _ _)

@[simp] lemma prob_output_simulate_eq_prob_output_simulate (z : α × S') :
  ⁅= z | simulate (so.mask_state mask) oa s'⁆ =
    ⁅= (z.1, mask.symm z.2) | simulate so oa (mask.symm s')⁆ :=
begin
  refine trans ((simulate_dist_equiv_map_simulate so mask oa s').prob_output_eq z)
    (prob_output_map_eq_single' _ _ _ (λ z' hz' h, h ▸ _));
  simp only [prod.map_mk, prod.map, apply_symm_apply, symm_apply_apply, prod.mk.eta, id.def]
end

lemma prob_event_simulate_eq_prob_event_simulate_comp (e : α × S' → Prop) :
  ⁅e | simulate (so.mask_state mask) oa s'⁆ =
    ⁅e ∘ prod.map id mask | simulate so oa (mask.symm s')⁆ :=
trans ((simulate_dist_equiv_map_simulate so mask oa s').prob_event_eq e) (prob_event_map _ _ _)

end simulate

section simulate'

variables (oa : oracle_comp spec α) (s' : S')

/-- Taking just the first result of simulating a computation with a masked simulation oracle
is equivalent to simulating with the original oracle after masking the initial state. -/
@[pairwise_dist_equiv] lemma simulate'_dist_equiv_simulate' :
  simulate' (so.mask_state mask) oa s' ≃ₚ simulate' so oa (mask.symm s') :=
by simp [simulate', function.comp]

@[simp] lemma support_simulate'_eq_support_simulate' :
  (simulate' (so.mask_state mask) oa s').support = (simulate' so oa (mask.symm s')).support :=
by pairwise_dist_equiv

@[simp] lemma fin_support_simulate'_eq_fin_support_simulate' [decidable_eq α] :
  (simulate' (so.mask_state mask) oa s').fin_support =
    (simulate' so oa (mask.symm s')).fin_support :=
by pairwise_dist_equiv

@[simp] lemma eval_dist_simulate'_eq_eval_dist_simulate' :
  ⁅simulate' (so.mask_state mask) oa s'⁆ = ⁅simulate' so oa (mask.symm s')⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_output_simulate'_eq_prob_output_simulate' (x : α) :
  ⁅= x | simulate' (so.mask_state mask) oa s'⁆ = ⁅= x | simulate' so oa (mask.symm s')⁆ :=
by pairwise_dist_equiv

@[simp] lemma prob_event_simulate'_eq_prob_event_simulate' (e : set α) :
  ⁅e | simulate' (so.mask_state mask) oa s'⁆ = ⁅e | simulate' so oa (mask.symm s')⁆ :=
by pairwise_dist_equiv

end simulate'

/-- Masking the state of a tracking oracle will produce another tracking oracle. -/
instance is_tracking (so : sim_oracle spec spec S) [hso : so.is_tracking] :
  (so.mask_state mask).is_tracking :=
⟨begin
  refine λ i t s, trans _ (is_tracking.fst_map_apply_eq_query so i t (mask.symm s)),
  rw [mask_state, map_map_eq_map_comp, prod.map],
  congr,
end⟩

end mask_state

end sim_oracle