/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_seed.generate_seed

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
then this will give a computation distributionally equivalent to the original computation. -/
def seeded_oracle (spec : oracle_spec) : sim_oracle spec spec (spec.query_seed) :=
λ i x, indexed_list.get_or_else x.2 i (query i x.1)

notation `seededₛₒ` := seeded_oracle _

namespace seeded_oracle

section apply

variables (i : spec.ι) (z : spec.domain i × spec.query_seed)

@[simp] protected lemma apply_eq : seededₛₒ i z = z.2.get_or_else i (query i z.1) := rfl

lemma apply_eq_of_mem_active_oracles (hi : i ∈ z.2.active_oracles) :
  seededₛₒ i z = return (z.2.pop i) := by simp [hi]

lemma apply_eq_of_not_mem_active_oracles (hi : i ∉ z.2.active_oracles) :
  seededₛₒ i z = (λ u, (u, z.2)) <$> query i z.1 := by simp [hi]

protected lemma apply_dist_equiv : seededₛₒ i z ≃ₚ z.2.get_or_else i (query i z.1) :=
dist_equiv.rfl

end apply

section generate_seed

-- /-- It's possible regenerate the remaining portion of the seed after simulating a computation with
-- the output of `generate_seed`, by generating a new seed of the appropriate size,
-- giving a still equivalent seed as before. -/
-- lemma generate_seed_bind_simulate_dist_equiv [h : is_sub_spec unif_spec spec]
--   (qc : spec.query_count) (oa : oracle_comp spec α) :
--   do {seed ← ↑(generate_seed qc), simulate seededₛₒ oa seed} ≃ₚ
--     do {seed ← ↑(generate_seed qc), z ← simulate seededₛₒ oa seed,
--       seed' ← ↑(generate_seed z.2.to_query_count), return (z.1, seed')} :=
-- begin

-- end

/-- If a query seed is generated by `generate_seed` and then used to simulate a computation,
the main output looks the same as just running the original computation. -/
lemma generate_seed_bind_simulate'_dist_equiv [h : is_sub_spec unif_spec spec]
  (qc : spec.query_count) (oa : oracle_comp spec α) :
  do {seed ← ↑(generate_seed qc), simulate' seededₛₒ oa seed} ≃ₚ oa :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing qc,
  {
    simp_rw [simulate'_return],
    pairwise_dist_equiv,
  },
  {
    simp_rw [simulate'_bind, simulate_query, seeded_oracle.apply_eq,
      indexed_list.get_or_else, ite_bind],
    simp at hoa,
    by_cases hi : i ∈ qc.active_oracles,
    {
      refine trans (bind_ite_dist_equiv_bind_left _ _ _ _ _) _,
      {
        intros qs hqs,
        rw [support_coe_sub_spec, support_generate_seed, set.mem_set_of_eq] at hqs,
        simpa only [← hqs] using hi,
      },
      {
        rw [← bind_assoc, ← oracle_comp.map_eq_bind_return_comp, ← coe_sub_spec_map],
        have := map_pop_generate_seed _ _ hi,
        rw [← coe_sub_spec_inj_dist_equiv unif_spec spec] at this,
        rw_dist_equiv [this],
        rw [coe_sub_spec_seq],
        simp,
        rw [bind_seq, oracle_comp.bind_map],
        simp [function.comp],
        rw_dist_equiv [hoa],
        refine bind_dist_equiv_bind_of_dist_equiv_left oa _,
        rw_dist_equiv [coe_sub_spec_dist_equiv],
        simp [dist_equiv.ext_iff, prob_output_query_eq_inv] }
    },
    {
      refine trans (bind_ite_dist_equiv_bind_right _ _ _ _ _) _,
      {
        intros qs hqs,
        rw [support_coe_sub_spec, support_generate_seed, set.mem_set_of_eq] at hqs,
        simpa only [← hqs] using hi,
      },
      {
        simp_rw [oracle_comp.bind_map],
        simp [function.comp],
        rw_dist_equiv [bind_bind_dist_equiv_comm, hoa],
      }
    }
  }
end

end generate_seed

end seeded_oracle