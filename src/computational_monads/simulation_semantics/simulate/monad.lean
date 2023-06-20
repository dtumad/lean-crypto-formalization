/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.map
import computational_monads.simulation_semantics.simulate.query


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

lemma support_simulate_map_bind (g : β → γ) : (simulate so (g <$> (oa >>= ob)) s).support =
  ⋃ x ∈ (simulate so oa s).support, prod.map g id '' (simulate so (ob $ prod.fst x) x.2).support :=
by simp only [support_simulate_map, support_simulate_bind, set.image_Union]

lemma eval_dist_simulate_map_bind (g : β → γ) : ⁅simulate so (g <$> (oa >>= ob)) s⁆ =
  ⁅simulate so oa s⁆.bind (λ x, ⁅simulate so (ob x.1) x.2⁆.map (prod.map g id)) :=
by simp only [simulate_map, simulate_bind, eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_simulate_map_bind' (g : β → γ) : ⁅simulate so (g <$> (oa >>= ob)) s⁆ =
  ⁅simulate so oa s⁆.bind (λ x, ⁅prod.map g id <$> simulate so (ob x.1) x.2⁆) :=
by simp only [simulate_map, simulate_bind, eval_dist_map, eval_dist_bind, pmf.map_bind]

lemma eval_dist_simulate_map_bind_apply [decidable_eq γ] [decidable_eq S]
  (g : β → γ) (z : γ × S) : ⁅simulate so (g <$> (oa >>= ob)) s⁆ z =
    ∑' (x : α × S), ⁅simulate so oa s⁆ x * ∑' (y : β),
      ite (z.1 = g y) (⁅simulate so (ob x.1) x.2⁆ (y, z.2)) 0 :=
begin
  sorry
end

end map_bind

section bind_map

lemma support_simulate_bind_map : (simulate so ((f <$> oa) >>= oc) s).support =
  ⋃ x ∈ (simulate so oa s).support, (simulate so (oc (f $ prod.fst x)) x.2).support :=
begin
  refine set.ext (λ z, _),
  simp only [support_simulate_bind, support_simulate_map, set.mem_image, set.Union_exists,
    set.Union_and, set.mem_Union],
  exact ⟨λ h, let ⟨x, y, hy, hxy, hx⟩ := h in ⟨y, hy, by simpa only [← hxy] using hx⟩,
    λ h, let ⟨x, hx, hz⟩ := h in ⟨(f x.1, x.2), x, hx, rfl, hz⟩⟩,
end


end bind_map

end oracle_comp