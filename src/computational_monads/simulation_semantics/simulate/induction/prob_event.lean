/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.induction.eval_dist

/-!
# Probability of Events After Simulation

This file contains more complex lemmas about `prob_event` applied to `simulate` and `simulate'`.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec
open_locale nnreal ennreal

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa oa' : oracle_comp spec α)
  (ob ob' : α → oracle_comp spec β) (s : S) (f : α → β)

-- lemma prob_event_simulate_eq_induction
--   {pr_e : Π (α : Type), oracle_comp spec α → S → set (α × S) → ℝ≥0}
--   (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
--   -- (h_ret : ∀ α a s, pr α (return a) s = pmf.pure (a, s))
--   -- (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
--   --   pr β (oa >>= ob) s = (pr α oa s).bind (λ x, pr β (ob x.1) x.2))
--   -- (h_query : ∀ i t s, pr (spec.range i) (query i t) s = ⁅so i (t, s)⁆) :
--   (e : set (α × S)) : ⁅e | simulate so oa s⁆ = pr_e α oa s e :=


end oracle_comp