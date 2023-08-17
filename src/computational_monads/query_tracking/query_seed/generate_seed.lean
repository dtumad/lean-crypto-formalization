/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.generate
import computational_monads.query_tracking.query_count.possible_outcomes
import computational_monads.query_tracking.query_seed.basic
import computational_monads.constructions.uniform_select

/-!
# Pre-Computation of Queries Made by a Computation

This file defines a function `generate_seed` that pre-computes a number of oracle outputs that can
be used in a computation, choosing them all uniformly at random.
The output is given by a `query_seed`, and the count is specified by a `query_count`.

If the number of seeded values is higher than the specified count the values remain unchanged.
The order in which the values are generated isn't specifically defined, as we use `finset.to_list`
to determine the ordering, and so the definition is noncomputable.
-/

namespace oracle_comp

open_locale big_operators
open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- Given a count of queries `qc`, and an initial `query_store` seed, generate more outputs at
random until the number of seeded outputs for each oracle is at least the value given in `qc`. -/
noncomputable def generate_seed (qc : spec.query_count) :
  oracle_comp uniform_selecting (spec.query_seed) :=
generate qc (λ i, $ᵗ (spec.range i))

variables (qc : spec.query_count) (qs : spec.query_seed)

lemma active_oracles_of_mem_support_generate_seed (qs : spec.query_seed)
  (hqs : qs ∈ (generate_seed qc).support) : qs.active_oracles = qc.active_oracles :=
begin
  sorry
end

@[simp] lemma mem_support_generate_seed_iff (qs : spec.query_seed) :
  qs ∈ (generate_seed qc).support ↔ ↑qs = qc :=
begin
  sorry,
end

@[simp] lemma prob_output_generate_seed (h : ↑qs = qc) :
  ⁅= qs | generate_seed qc⁆ = (possible_outcomes qc)⁻¹ :=
begin
  sorry
end

end oracle_comp