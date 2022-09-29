import computational_monads.simulation_semantics.simulate

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

open oracle_comp oracle_spec

namespace sim_oracle

/-- Mask the state value of an oracle, without changing the oracle's behaviour.
We capture this unchanged functionality by using an equivalence for the masking.
Convenient when working with composed or appended oracles, to remove unneeded state elements.
In particular `unit` state values that start spreading can be avoided.
-/
def mask_state (so : sim_oracle spec spec' S) (mask : S ≃ S') :
  sim_oracle spec spec' S' :=
{ default_state := mask so.default_state,
  o := λ i x, prod.map id mask <$> (so.o i $ prod.map id mask.symm x) }

variables (so : sim_oracle spec spec' S) (mask : S ≃ S') (mask' : S' ≃ S'')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (s : S) (s' : S') (s'' : S'')
  (x : spec.domain i × S') (y : spec.range i × S')

lemma apply_eq : so.mask_state mask i x =
  prod.map id mask <$> (so.o i $ prod.map id mask.symm x) := rfl

section support

/-- The `support` of a simulation with masked state is the same as the support without masking -/
@[simp]
theorem support_simulate_mask_eq_image_support_simulate :
  (simulate (so.mask_state mask) oa s').support =
    (prod.map id mask) '' (simulate so oa (mask.symm s')).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s',
  { simp_rw [simulate_return, support_return, prod_map, id.def,
      set.image_singleton, equiv.apply_symm_apply] },
  { refine set.ext (λ x, _),
    simp_rw [support_simulate_bind, hoa, set.image_Union, set.mem_Union, hob],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨⟨a, t⟩, ⟨⟨a', t'⟩, ⟨htas, hta⟩⟩, hx⟩ := h,
      rw [prod.map_mk, prod.eq_iff_fst_eq_snd_eq] at hta,
      have : mask.symm t = t' := (congr_arg _ hta.2.symm).trans (mask.symm_apply_apply t'),
      exact ⟨(a', mask.symm t), this.symm ▸ htas, hta.1.symm ▸ hx⟩ },
    { obtain ⟨⟨a, t⟩, hta, hx⟩ := h,
      exact ⟨(a, mask t), ⟨(a, t), hta, rfl⟩, (mask.symm_apply_apply t).symm ▸ hx⟩ } },
  { simpa only [simulate_query, apply_eq, support_map] }
end

lemma support_simulate_mask_eq_preimage_support_simulate :
  (simulate (so.mask_state mask) oa s').support =
    (prod.map id mask.symm) ⁻¹' (simulate so oa (mask.symm s')).support :=
begin
  rw [support_simulate_mask_eq_image_support_simulate],
  refine congr_fun (set.image_eq_preimage_of_inverse _ _) _;
  exact λ x, by simp only [prod_map, id.def, equiv.symm_apply_apply,
    equiv.apply_symm_apply, prod.mk.eta]
end

/-- The `support` of a regular simulation can be represented as the image of a simulation
with a masked state, with the image applying an unmask function for the masking -/
lemma support_simulate_eq_image_support_simulate_mask : (simulate so oa s).support =
  (prod.map id mask.symm) '' (simulate (so.mask_state mask) oa (mask s)).support :=
by simp_rw [support_simulate_mask_eq_image_support_simulate, set.image_image, prod.map_map,
  equiv.symm_comp_self, equiv.symm_apply_apply, function.comp.right_id, prod.map_id, set.image_id]

lemma support_simulate_eq_preimage_support_simulate_mask : (simulate so oa s).support =
  (prod.map id mask) ⁻¹' (simulate (so.mask_state mask) oa (mask s)).support :=
by simp_rw [support_simulate_mask_eq_preimage_support_simulate, set.preimage_preimage,
  prod.map_map, equiv.symm_comp_self, equiv.symm_apply_apply, function.comp.right_id,
    prod.map_id, set.preimage_id]

@[simp]
lemma support_simulate'_mask_eq_support_simulate' :
  (simulate' (so.mask_state mask) oa s').support = (simulate' so oa (mask.symm s')).support :=
by simpa only [support_simulate', support_simulate_mask_eq_image_support_simulate, set.image_image]

lemma support_simulate'_eq_support_simulate'_mask :
  (simulate' so oa s).support = (simulate' (so.mask_state mask) oa (mask s)).support :=
by rw [support_simulate'_mask_eq_support_simulate', equiv.symm_apply_apply]

lemma support_simulate_mask_mask_eq_support_simulate_mask_comp :
  (simulate ((so.mask_state mask).mask_state mask') oa s'').support =
    (simulate (so.mask_state $ mask.trans mask') oa s'').support :=
by simpa only [support_simulate_mask_eq_image_support_simulate, set.image_image, prod.map_map,
  equiv.symm_trans_apply, function.comp.right_id]

end support

section fin_support

variables [computable spec'] [finite_range spec'] [decidable oa]

end fin_support

section distribution_semantics

open distribution_semantics

variable [spec'.finite_range]

section eval_dist

@[simp]
lemma eval_dist_apply : ⦃(so.mask_state mask) i (t, s')⦄ =
  (⦃so i (t, mask.symm s')⦄).map (prod.map id mask) :=
by simpa only [apply_eq, eval_dist_map]

@[simp]
theorem eval_dist_simulate_mask : ⦃simulate (so.mask_state mask) oa s'⦄
  = (⦃simulate so oa (mask.symm s')⦄).map (prod.map id mask) :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s',
  { simp only [pmf.pure_map, simulate_return, eval_dist_return,
      prod.map_mk, id.def, equiv.apply_symm_apply] },
  { simp_rw [eval_dist_simulate_bind, hoa, hob, pmf.map_bind, pmf.bind_map],
    refine congr_arg _ (funext $ λ x, _),
    simp only [function.comp_app, prod_map, id.def, equiv.symm_apply_apply] },
  { simp only [eval_dist_apply, simulate_query] }
end

@[simp]
lemma eval_dist_simulate_mask_apply (x : α × S') : ⦃simulate (so.mask_state mask) oa s'⦄ x =
  ⦃simulate so oa (mask.symm s')⦄ (x.1, mask.symm x.2) :=
begin
  simp only [eval_dist_simulate_mask, pmf.map_apply],
  refine (tsum_eq_single (x.1, mask.symm x.2) $ λ y hy, _).trans _,
  { have : x ≠ prod.map id ⇑mask y := λ hx, hy (by rw [hx, prod.map_fst, prod.map_snd,
      equiv.symm_apply_apply, id.def, prod.mk.eta]),
    simp_rw [this, if_false] },
  { simp only [prod.map_mk, id.def, equiv.apply_symm_apply, prod.mk.eta,
      eq_self_iff_true, if_true] }
end

end eval_dist

section equiv

end equiv

section prob_event

@[simp]
theorem prob_event_simulate_mask_eq_preimage (e : set (α × S')) :
  ⦃e | simulate (so.mask_state mask) oa s'⦄ =
    ⦃(prod.map id mask) ⁻¹' e | simulate so oa (mask.symm s')⦄ :=
by simp_rw [prob_event_eq_to_nnreal_to_outer_measure_apply,
  eval_dist_simulate_mask, pmf.to_outer_measure_map_apply]

lemma prob_event_simulate_mask_eq_image (e : set (α × S')) :
  ⦃e | simulate (so.mask_state mask) oa s'⦄ =
    ⦃(prod.map id mask.symm) '' e | simulate so oa (mask.symm s')⦄ :=
begin
  convert (prob_event_simulate_mask_eq_preimage so mask oa s' e),
  ext x,
  simp only [prod_map, id.def, set.mem_image, set.mem_preimage],
  exact ⟨λ ⟨x', hx'⟩, by simpa only [← hx'.2, equiv.apply_symm_apply, prod.mk.eta] using hx'.1,
    λ h, ⟨(x.1, mask x.2), h, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, equiv.symm_apply_apply _ _⟩⟩⟩
end

end prob_event

end distribution_semantics

end sim_oracle