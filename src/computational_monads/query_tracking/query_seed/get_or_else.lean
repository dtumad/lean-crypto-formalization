/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_seed.basic
import computational_monads.query_tracking.query_count.possible_outcomes
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

namespace query_seed

variables {α β γ : Type} {spec : oracle_spec}

def get_or_else (qs : query_seed spec) (i : spec.ι) (t : spec.domain i) :
  oracle_comp spec (spec.range i × query_seed spec) :=
match qs i with
| [] := do {u ← query i t, return (u, qs)}
| (u :: us) := return (u, qs.drop_queries i 1)
end

@[simp] lemma get_or_else_empty (i : spec.ι) (t : spec.domain i) :
  get_or_else ∅ i t = do {u ← query i t, return (u, ∅)} :=
by simp only [get_or_else, query_seed.empty_apply]

end query_seed

end oracle_comp