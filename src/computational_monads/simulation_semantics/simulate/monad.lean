/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.map

/-!
# Distribution Semantics of Simulated Computations

This file contains more complex lemmas about the `eval_dist` of `simulate` and `simulate'`,
when the computation is some more complex monadic construction.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa oa' : oracle_comp spec α)
  (ob ob' : α → oracle_comp spec β) (oc : β → oracle_comp spec γ) (s : S) (f : α → β)

section map_bind

variable (g : β → γ)

@[simp] lemma support_simulate_map_bind : (simulate so (g <$> (oa >>= ob)) s).support =
  ⋃ x ∈ (simulate so oa s).support, prod.map g id '' (simulate so (ob $ prod.fst x) x.2).support :=
by simp only [support_simulate_map, support_simulate_bind, set.image_Union]

@[simp] lemma eval_dist_simulate_map_bind : ⁅simulate so (g <$> (oa >>= ob)) s⁆ =
  ⁅simulate so oa s⁆.bind (λ x, ⁅simulate so (ob x.1) x.2⁆.map (prod.map g id)) :=
by simp only [simulate_map, simulate_bind, eval_dist_map, eval_dist_bind, pmf.map_bind]

@[pairwise_dist_equiv] lemma simulate_map_bind_dist_equiv : simulate so (g <$> (oa >>= ob)) s ≃ₚ
  simulate so oa s >>= λ x, prod.map g id <$> simulate so (ob x.1) x.2 :=
by pairwise_dist_equiv

@[simp] lemma prob_output_simulate_map_bind [decidable_eq γ] [decidable_eq S]
  (z : γ × S) : ⁅= z | simulate so (g <$> (oa >>= ob)) s⁆ =
    ∑' (x : α × S), (⁅= x | simulate so oa s⁆ *
      ∑' (y : β), ite (z.1 = g y) ⁅= (y, z.2) | simulate so (ob x.1) x.2⁆ 0) :=
begin
  refine trans ((simulate_map_bind_dist_equiv _ _ _ s g).prob_output_eq z) _,
  simp [prob_output_bind_eq_tsum, prob_output_map_prod_map_id_right],
end

end map_bind

section bind_map

@[simp] lemma support_simulate_bind_map : (simulate so ((f <$> oa) >>= oc) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (oc (f $ prod.fst x)) x.2).support :=
begin
  refine set.ext (λ z, _),
  simp only [support_simulate_bind, support_simulate_map, set.mem_image, set.Union_exists,
    set.Union_and, set.mem_Union],
  exact ⟨λ h, let ⟨x, y, hy, hxy, hx⟩ := h in ⟨y, hy, by simpa only [← hxy] using hx⟩,
    λ h, let ⟨x, hx, hz⟩ := h in ⟨(f x.1, x.2), x, hx, rfl, hz⟩⟩,
end

end bind_map

section return_bind

lemma simulate_return_bind_dist_equiv : simulate so (return a >>= ob) s ≃ₚ simulate so (ob a) s :=
by pairwise_dist_equiv

lemma support_simulate_return_bind : (simulate so (return a >>= ob) s).support =
  (simulate so (ob a) s).support := by pairwise_dist_equiv

lemma fin_support_simulate_return_bind : (simulate so (return a >>= ob) s).fin_support =
  (simulate so (ob a) s).fin_support := by pairwise_dist_equiv

lemma eval_dist_simulate_return_bind : ⁅simulate so (return a >>= ob) s⁆ =
  ⁅simulate so (ob a) s⁆ := by pairwise_dist_equiv

lemma prob_output_simulate_return_bind (z : β × S) : ⁅= z | simulate so (return a >>= ob) s⁆ =
  ⁅= z | simulate so (ob a) s⁆ := by pairwise_dist_equiv

lemma prob_event_simulate_return_bind (e : set (β × S)) : ⁅e | simulate so (return a >>= ob) s⁆ =
  ⁅e | simulate so (ob a) s⁆ := by pairwise_dist_equiv

end return_bind

end oracle_comp