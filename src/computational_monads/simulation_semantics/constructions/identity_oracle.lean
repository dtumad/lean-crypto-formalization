/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_stateless

/-!
# Identity Oracle

Defines a `sim_oracle` that just acts as an identity,
  e.g. simulation with this oracle has no effect (besides an empty state)

Main use cases is in simulating a pair of oracles, where only one of the oracles is reduced.
  For example preserving a `uniform_selecting` oracle while reducing a `signing_oracle`
-/

open oracle_comp oracle_spec

variables {α β : Type} {spec spec' spec'' : oracle_spec}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s : unit)

@[inline, reducible]
def identity_oracle (spec : oracle_spec) : sim_oracle spec spec unit := ⟪query⟫

notation `idₛ` := identity_oracle _

namespace identity_oracle

@[simp] lemma apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  (idₛ) i (t, s) = query i t >>= λ u, return (u, ()) := rfl

section support

@[simp] lemma support_apply (i : spec.ι) (t : spec.domain i) :
  ((idₛ) i (t, s)).support = {u | u.1 ∈ (query i t).support} :=
begin
  simp only [apply, support_bind, support_return, set.Union_true,
    set.Union_singleton_eq_range, support_query, set.top_eq_univ, set.mem_univ, set.set_of_true],
  exact set.eq_univ_of_forall (λ x, set.mem_range.2
    ⟨x.1, prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, punit_eq () x.snd⟩⟩),
end

@[simp] lemma support_simulate' : (simulate' idₛ oa s).support = oa.support :=
stateless_oracle.support_simulate'_eq_support _ query s (λ _ _, rfl)

@[simp] lemma support_simulate : (simulate idₛ oa s).support = prod.fst ⁻¹' oa.support :=
(stateless_oracle.support_simulate_eq_preimage_support_simulate' _ _ _).trans
  (congr_arg _ $ support_simulate' oa ())

@[simp] lemma mem_support_simulate_iff (x : α × unit) :
  x ∈ (simulate idₛ oa s).support ↔ x.1 ∈ oa.support :=
by rw [support_simulate, set.mem_preimage]

end support

section distribution_semantics

section eval_dist

@[simp]
lemma eval_dist_apply (i : spec.ι) (t : spec.domain i) :
  ⁅idₛ i (t, s)⁆ = ⁅(λ u, (u, ())) <$> query i t⁆ :=
rfl

-- @[simp]
-- lemma eval_dist_simulate : ⁅simulate idₛ oa s⁆ = ⁅(λ a, (a, ())) <$> oa⁆ :=
-- begin
--   induction oa with α a α β oa ob hoa hob i t generalizing s,
--   { simp [punit_eq s (), pmf.pure_map] },
--   { exact trans (simulate_bind_equiv idₛ oa ob s) (trans (eval_dist_bind_eq_of_eval_dist_eq
--       (hoa s) (λ x, hob x.fst x.snd)) (by simp)) },
--   { exact (simulate_query_equiv idₛ i t ()).trans (apply_equiv () i t) }
-- end

-- lemma eval_dist_default_simulate : default_simulate idₛ oa ≃ₚ (λ a, (a, ())) <$> oa :=
-- simulate_equiv oa ()

-- @[simp]
-- lemma simulate'_equiv : (simulate' idₛ oa s) ≃ₚ oa :=
-- calc simulate' idₛ oa s ≃ₚ prod.fst <$> simulate idₛ oa s : rfl
--   ... ≃ₚ prod.fst <$> (λ a, (a, ())) <$> oa : (map_equiv_of_equiv _ (simulate_equiv oa s))
--   ... ≃ₚ (prod.fst ∘ λ a, (a, ())) <$> oa : map_map_equiv oa _ _
--   ... ≃ₚ oa : map_id_equiv oa

-- lemma default_simulate'_equiv : default_simulate' idₛ oa ≃ₚ oa :=
-- simulate'_equiv oa ()

end eval_dist

section prob_event



end prob_event

end distribution_semantics

end identity_oracle