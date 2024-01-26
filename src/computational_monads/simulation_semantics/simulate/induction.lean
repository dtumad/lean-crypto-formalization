/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad

/-!
# Induction Lemmas for Oracle Simulation

This file contains convenience lemmas for showing that the distribution semantics
of `simulate so oa s` take a certain form via induction on `oa`.
The only difference between direct induction on `oa` is that it pre-emptively simplifies
the applications of `simulate` and the other side.

TODO: would be nice to have versions analogous to `oracle_comp.induction_on'` as well.
-/

namespace oracle_comp

open_locale ennreal
open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} {S S' : Type}

section support

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind`. -/
lemma support_simulate_eq_induction {supp : Π (α : Type), oracle_comp spec α → S → set (α × S)}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, supp α (return a) s = {(a, s)})
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    supp β (oa >>= ob) s = ⋃ x ∈ (supp α oa s), supp β (ob $ prod.fst x) $ prod.snd x)
  (h_query : ∀ i t s, supp (spec.range i) (query i t) s = (so i (t, s)).support) :
  (simulate so oa s).support = supp α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate_return, support_return] },
  { simp only [simulate_bind, support_bind, hoa, hob, h_bind] },
  { simp only [h_query, simulate_query] }
end

/-- Version of `support_simulate_eq_induction` for `simulate'` -/
lemma support_simulate'_eq_induction {supp : Π (α : Type), oracle_comp spec α → S → set α}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, supp α (return a) s = {a})
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    supp β (oa >>= ob) s = ⋃ x ∈ (simulate so oa s).support, supp β (ob $ prod.fst x) $ prod.snd x)
  (h_query : ∀ i t s, supp (spec.range i) (query i t) s = prod.fst '' (so i (t, s)).support) :
  (simulate' so oa s).support = supp α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate'_return, support_map, support_return, set.image_singleton] },
  { simp only [h_bind, ←hob, simulate'_bind, support_map, support_simulate', support_bind] },
  { simp only [h_query, simulate'_query, support_map] }
end

end support

section dist_equiv

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind` -/
lemma simulate_dist_equiv_induction
  {pr : Π (α : Type), oracle_comp spec α → S → oracle_comp spec' (α × S)}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, pr α (return a) s ≃ₚ return' !spec'! (a, s))
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    pr β (oa >>= ob) s ≃ₚ pr α oa s >>= λ x, pr β (ob x.1) x.2)
  (h_query : ∀ i t s, pr (spec.range i) (query i t) s ≃ₚ so i (t, s)) :
  simulate so oa s ≃ₚ pr α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a' α β oa ob hoa hob i t generalizing s,
  { rw_dist_equiv [h_ret] },
  { rw_dist_equiv [simulate_bind_dist_equiv, h_bind, hoa, hob] },
  { simpa only [simulate_query] using symm (h_query i t s) }
end

end dist_equiv

section eval_dist

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind` -/
lemma eval_dist_simulate_eq_induction {pr : Π (α : Type), oracle_comp spec α → S → (pmf (α × S))}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, pr α (return a) s = pmf.pure (a, s))
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    pr β (oa >>= ob) s = (pr α oa s).bind (λ x, pr β (ob x.1) x.2))
  (h_query : ∀ i t s, pr (spec.range i) (query i t) s = ⁅so i (t, s)⁆) :
  ⁅simulate so oa s⁆ = pr α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a' α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate_return, eval_dist_return] },
  { simp only [h_bind, hoa, hob, simulate_bind, eval_dist_bind] },
  { simp only [h_query, simulate_query] }
end

end eval_dist

section prob_output

/-- Lemma for inductively proving that the distribution associated to a simulation
is a specific function. Gives more explicit criteria than induction on the computation.
In particular this automatically splits the cases for `return` and the `prod` in the `bind` sum. -/
lemma prob_output_simulate_eq_induction
  {pr : Π (α : Type), oracle_comp spec α → S → α × S → ℝ≥0∞}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S) (a : α) (s' : S)
  (h_ret : ∀ α a s, pr α (return a) s (a, s) = 1)
  (h_ret' : ∀ α a a' s s', a ≠ a' ∨ s ≠ s' → pr α (return a) s (a', s') = 0)
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s b s',
    pr β (oa >>= ob) s (b, s') = ∑' (a : α) (t : S), (pr α oa s (a, t)) * (pr β (ob a) t (b, s')))
  (h_query : ∀ i t s u s', pr (spec.range i) (query i t) s (u, s') = ⁅so i (t, s)⁆ (u, s')) :
  ⁅= (a, s') | simulate so oa s⁆ = pr α oa s (a, s') :=
begin
  induction oa using oracle_comp.induction_on with α a' α β oa ob hoa hob i t generalizing s s',
  { rw [prob_output_simulate_return_eq_indicator, set.indicator],
    split_ifs with has,
    { simp only [set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq] at has,
      refine has.1 ▸ has.2.symm ▸ (h_ret α a s).symm, },
    { simp only [set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq, not_and_distrib] at has,
      cases has with ha hs,
      { exact (h_ret' α a' a s s' $ or.inl $ ne.symm ha).symm },
      { exact (h_ret' α a' a s s' $ or.inr $ ne.symm hs).symm } } },
  { simp only [prob_output_simulate_bind_eq_tsum_tsum, h_bind, hoa, hob] },
  { rw [simulate_query, h_query, eval_dist_apply_eq_prob_output] },
end

end prob_output

section prob_event


end prob_event

end oracle_comp