/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.possible_outcomes
import computational_monads.constructions.repeat

/-!
# Generate an Indexed List by Running a Computation According to a Count

This file defines a function `generate` for running a computation multiple times based
on a given `query_count`, generating an indexed list of the output types.
Any result will have the same "shape" as the original count, in the sense that it coerces
back to the original count under `indexed_list.coe_query_count`.
-/

namespace oracle_comp

open_locale big_operators
open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec} {τ τ' : spec.ι → Type}

def generate_aux (qc : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i)) :
  list spec.ι → oracle_comp spec' (spec.indexed_list τ)
| (j :: js) := do { ts ← repeat (oa j) (qc.get_count j),
    tss ← generate_aux js, return (tss.add_values ts.to_list) }
| [] := return ∅

/-- Run a computation `oa` for each of the active oracles in the query count `qc`,
aggregating the results into an indexed list. -/
noncomputable def generate (qc : spec.query_count)
  (oa : Π (i : spec.ι), oracle_comp spec' (τ i)) : oracle_comp spec' (spec.indexed_list τ) :=
generate_aux qc oa qc.active_oracles.to_list

variables (qc : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i))

lemma mem_support_generate_iff (il : spec.indexed_list τ) : il ∈ (generate qc oa).support ↔
  ∀ i ∈ il.active_oracles, list.all₂ (λ x, x ∈ (oa i).support) (il i) :=
begin
  sorry
end

end oracle_comp