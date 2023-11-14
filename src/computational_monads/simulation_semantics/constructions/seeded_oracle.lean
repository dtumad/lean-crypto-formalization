/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_seed.generate_seed
import computational_monads.query_tracking.indexed_list.get_or_else
import computational_monads.simulation_semantics.oracle_compose
import computational_monads.coercions.instances
import computational_monads.asymptotics.polynomial_queries

/-!
# Seeded Simulation Oracle

This file constructs a simulation oracle that allows for a set of predetermined query responses.
The oracle takes a `query_log` as an initial state, and uses the internal values
to respond to queries, and then forwards any additional queries back to the original oracle.
Note that if any query fails to find a seed value, the entire `query_log` is discarded,
regardless of if further values exist for oracles of different indices.

This can more generally be thought of as a form of small-step semantics for `oracle_comp`,
evaluating the computation using the provided value, eventually reducing to a single value,
unless it runs out of values in which case it returns a only a partial computation.
If the initial seed is larger than a query bound on the computation it will always finish.
-/

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {α β γ : Type}

/-- Run a computation by using a `query_seed` to answer queries when possible, and making new
queries if there isn't a seed value. If the `query_seed` comes from executing `generate_seed`
then this will give a computation distributionally equivalent to the original computation.

TODO: `seeded_sim_oracle`? `uniform_selecting` --> `uniform_oracle` -/
noncomputable def seeded_oracle (spec : oracle_spec) : sim_oracle spec spec (spec.query_seed) :=
{ o := λ i x, indexed_list.get_or_else x.2 i (query i x.1),
  default_state := ∅ }

notation `seededₛₒ` := seeded_oracle _

namespace seeded_oracle

section apply

variables (i : spec.ι) (z : spec.domain i × spec.query_seed)

@[simp] protected lemma apply_eq : seededₛₒ i z = z.2.get_or_else i (query i z.1) := rfl

@[pairwise_dist_equiv] protected lemma apply_dist_equiv :
  seededₛₒ i z ≃ₚ z.2.get_or_else i (query i z.1) :=
dist_equiv_of_eq (seeded_oracle.apply_eq i z)

end apply

/-- It's possible regenerate the remaining portion of the seed after simulating a computation with
the output of `generate_seed`, by generating a new seed of the appropriate size,
giving a still equivalent seed as before. -/
lemma generate_seed_bind_simulate_dist_equiv [h : is_sub_spec uniform_selecting spec]
  (qc : spec.query_count) (oa : oracle_comp spec α) :
  do {seed ← ↑(generate_seed qc), simulate seededₛₒ oa seed} ≃ₚ
    do {seed ← ↑(generate_seed qc), z ← simulate seededₛₒ oa seed,
      seed' ← ↑(generate_seed z.2.to_query_count), return (z.1, seed')} :=
begin
  sorry
end

/-- If a query seed is generated by `generate_seed` and then used to simulate a computation,
the main output looks the same as just running the original computation. -/
lemma generate_seed_bind_simulate'_dist_equiv [h : is_sub_spec uniform_selecting spec]
  (qc : spec.query_count) (oa : oracle_comp spec α) :
  do {seed ← ↑(generate_seed qc), simulate' seededₛₒ oa seed} ≃ₚ oa :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing qc,
  {
    rw_dist_equiv [simulate'_return_dist_equiv, bind_const_dist_equiv]
  },
  { sorry,
    -- rw_dist_equiv [simulate'_bind_dist_equiv, bind_bind_dist_equiv_assoc,
    --   generate_seed_bind_simulate_dist_equiv],
    -- simp_rw_dist_equiv [bind_bind_dist_equiv_assoc],
    -- sorry,
  },
  {
    rw_dist_equiv [simulate'_query_dist_equiv, seeded_oracle.apply_dist_equiv,
      indexed_list.get_or_else_dist_equiv, map_ite_dist_equiv],
    simp only,
    by_cases hi : i ∈ qc.active_oracles,
    {
      refine trans (bind_ite_dist_equiv_bind_left _ _ _ _ (λ qs hqs, _)) _,
      {
        rw [support_coe_sub_spec, support_generate_seed] at hqs,
        simp only [indexed_list.coe_query_count_eq, set.mem_set_of_eq] at hqs,
        rw [← hqs, indexed_list.active_oracles_to_query_count] at hi,
        exact hi,
      },
      {
        rw_dist_equiv [map_return_dist_equiv],
        rw [oracle_comp.bind_return_comp_eq_map],
        rw [map_coe_sub_spec_dist_equiv_iff],
        rw_dist_equiv [map_fst_get_head_generate_seed_dist_equiv _ _ hi],
        pairwise_dist_equiv,
      },
    },
    {
      refine trans (bind_ite_dist_equiv_bind_right _ _ _ _ (λ qs hqs, _)) _,
      {
        rw [support_coe_sub_spec, support_generate_seed] at hqs,
        simp only [indexed_list.coe_query_count_eq, set.mem_set_of_eq] at hqs,
        rw [← hqs, indexed_list.active_oracles_to_query_count] at hi,
        exact hi,
      },
      {
        rw_dist_equiv [map_comp_dist_equiv, map_id_dist_equiv,
          bind_const_dist_equiv],
      }
    }
  }
end

lemma queries_at_most_simulate (qc : spec.query_count) (oa : oracle_comp spec α)
  (h : oa.queries_at_most qc) (qs : query_seed spec) :
  (simulate seededₛₒ oa qs).queries_at_most (qc - ↑qs) :=
begin
  sorry
end

end seeded_oracle