/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.monad

/-!
# Miscellaneous Lemmas About Distribution Semantics

This file contains lemmas about `eval_dist` and `prob_event` that don't fit anywhere else.
Ideally these lemmas should eventually be ported to a more dedicated file,
but this is meant as a temprorary location for specific lemmas without a fleshed out background.
-/

namespace oracle_comp

open oracle_spec
open_locale big_operators ennreal

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Write the `eval_dist` of bind as a sum over another type,
using a map that is both injective and surjective on corresponding supports,
although it may not actually be bijective on the entire spaces. -/
lemma prob_output_bind_of_inj_on_support {oa : oracle_comp spec α}
  {ob : α → oracle_comp spec β} {b : β} (g : γ → α)
  (h : ∀ x ∈ oa.support, b ∈ (ob x).support → x ∈ set.range g)
  (hg : ∀ x y, g x = g y → g x ∈ oa.support → b ∈ (ob (g x)).support → x = y) :
  ⁅= b | oa >>= ob⁆ = ∑' (c : γ), ⁅= g c | oa⁆ * ⁅= b | ob (g c)⁆ :=
begin
  rw [prob_output_bind_eq_tsum],
  refine tsum_eq_tsum_of_ne_zero_bij (g ∘ coe) _ _ (λ _, rfl),
  { intros x y h,
    have := x.2,
    simp only [subtype.val_eq_coe, function.support_mul, set.mem_inter_iff, function.mem_support,
      ne.def, prob_output_eq_zero_iff, set.not_not_mem] at this,
    refine hg ↑x ↑y h this.1 this.2 },
  { intros x hx,
    simp only [function.support_mul, set.mem_inter_iff, function.mem_support, ne.def,
      prob_output_eq_zero_iff, set.not_not_mem] at hx,
    specialize h x hx.1 hx.2,
    rw [set.mem_range] at h,
    obtain ⟨y, hy⟩ := h,
    rw [← hy, set.range_comp, set.mem_image],
    refine ⟨y, _, rfl⟩,
    rw [subtype.range_coe_subtype],
    simp only [hy, hx, function.support_mul, set.mem_inter_iff, function.mem_support,
      ne.def, prob_output_eq_zero_iff, set.not_not_mem, set.mem_set_of_eq, true_and] }
end

end oracle_comp