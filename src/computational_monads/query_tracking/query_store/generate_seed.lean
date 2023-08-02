/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_store.basic
import computational_monads.constructions.repeat
import computational_monads.constructions.uniform_select

/-!
# Structure for Bounding Number of Queries Made by a Computation

This file defines a function `generate_seed` that pre-computes a number of oracle outputs that can
be used in a computation, choosing them all uniformly at random.
The output is given by a `query_store`, and the count is specified by a `query_count`.

If the number of seeded values is higher than the specified count the values remain unchanged.
The order in which the values are generated isn't specifically defined, as we use `finset.to_list`
to determine the ordering, and so the definition is noncomputable.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

/-- Helper function to perform the recursion in `generate_seed`. -/
private noncomputable def generate_seed_aux (qc : query_count spec) (seed : query_store spec) :
  list spec.ι → oracle_comp uniform_selecting (query_store spec)
| list.nil := return seed
| (i :: ql) := do { ts ← repeat ($ᵗ (spec.range i)) (qc.get_count i - (seed.get_store i).length),
                    return (seed.log_query_list ts.to_list) }

/-- Given a count of queries `qc`, and an initial `query_store` seed, generate more outputs at
random until the number of seeded outputs for each oracle is at least the value given in `qc`. -/
noncomputable def generate_seed (qc : query_count spec) (seed : query_store spec) :
  oracle_comp uniform_selecting (query_store spec) :=
generate_seed_aux qc seed qc.active_oracles.to_list

variables (qc : query_count spec) (seed seed' : query_store spec)

lemma mem_support_generate_seed_iff :
  seed' ∈ (generate_seed qc seed).support ↔ seed'.to_query_count = qc :=
begin
  sorry,
end

end oracle_comp