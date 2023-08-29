/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.counting_oracle
import data.polynomial.eval

/-!
# Query Bounds for Oracle Computations

This file defines a proposition `queries_at_most` to bound the number of queries made by a
computation, and a structure `poly_num_queries` to show that a indexed set of computations
have number of queries bounded by a polynomial in the index.
-/

namespace oracle_comp

open oracle_spec

variables {α β : Type} {spec spec' : oracle_spec}

section queries_at_most

/-- A `query_count` bounds the number of queries made by a computation if any result of simulating
with `countingₛₒ produces a count that is smaller. -/
def queries_at_most (oa : oracle_comp spec α) (qc : spec.query_count) : Prop :=
∀ x qc', (x, qc') ∈ (simulate countingₛₒ oa ∅).support → qc' ≤ qc

/-- The number of queries made by `return a` is bounded by any count. -/
@[simp] lemma queries_at_most_return (a : α) (qc : spec.query_count) :
  (return' !spec! a).queries_at_most qc :=
begin
  intros x qc' h,
  simp only [support_simulate_return, set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq] at h,
  exact h.2.symm ▸ (indexed_list.empty_le qc)
end

@[simp] lemma queries_at_most_query_iff (i : spec.ι) (t : spec.domain i) (qc : spec.query_count) :
  (query i t).queries_at_most qc ↔ i ∈ qc.active_oracles :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    specialize h default qc,
    sorry,

  },
  {
    sorry,
  }
end

end queries_at_most

section poly_num_queries

/-- If `f` is an `oracle_comp` indexed by a security parameter, then `poly_num_queries f` means
that for each oracle there exists a polynomial that bounds the number of queries to that oracle,
as a function of the input parameter. -/
structure poly_num_queries (f : ℕ → oracle_comp spec α) :=
(qc : ℕ → spec.query_count)
(queries_at_most_qc (n : ℕ) : queries_at_most (f n) (qc n))
(poly_bound (i : spec.ι) : polynomial ℕ)
(queries_le_poly_bound (n : ℕ) (i : spec.ι) : (qc n).get_count i ≤ (poly_bound i).eval n)

end poly_num_queries

end oracle_comp