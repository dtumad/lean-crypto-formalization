/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_seed.get_or_else
import computational_monads.query_tracking.query_count.possible_outcomes
import computational_monads.constructions.repeat
import computational_monads.constructions.uniform_select

/-!
# Structure for Bounding Number of Queries Made by a Computation

This file defines a function `generate_seed` that pre-computes a number of oracle outputs that can
be used in a computation, choosing them all uniformly at random.
The output is given by a `query_seed`, and the count is specified by a `query_count`.

If the number of seeded values is higher than the specified count the values remain unchanged.
The order in which the values are generated isn't specifically defined, as we use `finset.to_list`
to determine the ordering, and so the definition is noncomputable.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

-- def seed_set_aux (qc : query_count spec) (seed_set : set (query_seed spec)) :
--   list spec.ι → set (query)

/-- Helper function to perform the recursion in `generate_seed`. -/
private noncomputable def generate_seed_aux (qc : query_count spec) :
  query_seed spec → list spec.ι → oracle_comp uniform_selecting (query_seed spec)
| seed list.nil := return seed
| seed (i :: ql) := do { ts ← repeat ($ᵗ (spec.range i)) (qc i),
    generate_seed_aux (seed.seed_queries ts.to_list) ql }

variables (qc : query_count spec) (seed : query_seed spec)

@[simp] lemma generate_seed_aux_nil : generate_seed_aux qc seed [] = return seed := rfl

@[simp] lemma generate_seed_aux_cons (i : spec.ι) (ql : list spec.ι) :
  generate_seed_aux qc seed (i :: ql) = do { ts ← repeat ($ᵗ (spec.range i)) (qc i),
    generate_seed_aux qc (seed.seed_queries ts.to_list) ql } := by rw [generate_seed_aux]

/-- Given a count of queries `qc`, and an initial `query_store` seed, generate more outputs at
random until the number of seeded outputs for each oracle is at least the value given in `qc`. -/
noncomputable def generate_seed (qc : query_count spec) :
  oracle_comp uniform_selecting (query_seed spec) :=
generate_seed_aux qc ∅ qc.active_oracles.to_list

@[simp] lemma mem_support_generate_seed_empty_iff :
  seed ∈ (generate_seed qc).support ↔ seed.to_query_count = qc :=
begin
  simp only [fun_like.ext_iff, query_seed.to_query_count_apply_eq_length],
  sorry,
end

@[simp] lemma prob_output_generate_seed (h : seed.to_query_count = qc) :
  ⁅= seed | generate_seed qc⁆ = (possible_outcomes qc)⁻¹ :=
begin
  sorry
end



end oracle_comp