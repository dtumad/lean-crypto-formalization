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

open_locale big_operators
open oracle_spec

variables {α β γ : Type} {spec : oracle_spec}
  (qc : query_count spec) (seed : query_seed spec)
  (j : spec.ι) (js : list spec.ι)

section generate_seed_aux

/-- Helper function to perform the recursion in `generate_seed`. -/
private noncomputable def generate_seed_aux (qc : query_count spec) :
  query_seed spec → list spec.ι → oracle_comp uniform_selecting (query_seed spec)
| seed list.nil := return seed
| seed (j :: js) := do {ts ←$ᵗ (vector (spec.range j) (qc j)),
    generate_seed_aux (seed.seed_queries ts.to_list) js}

@[simp] lemma generate_seed_aux_nil : generate_seed_aux qc seed [] = return seed := rfl

@[simp] lemma generate_seed_aux_cons : generate_seed_aux qc seed (j :: js) =
  do {ts ←$ᵗ (vector (spec.range j) (qc j)),
    generate_seed_aux qc (seed.seed_queries ts.to_list) js} :=
by rw [generate_seed_aux]

lemma active_oracles_of_mem_support_generate_seed_aux {qc seed js}
  (qs : query_seed spec) (hqs : qs ∈ (generate_seed_aux qc seed js).support) :
  qs.active_oracles = seed.active_oracles ∪ {j ∈ qc.active_oracles | j ∈ js} :=
begin
  induction js with j js hj generalizing seed,
  { rw [generate_seed_aux_nil, mem_support_return_iff] at hqs,
    simp [hqs] },
  { simp [generate_seed_aux_cons, support_bind] at hqs,
    obtain ⟨ks, hks⟩ := hqs,
    refine (hj hks).trans (finset.ext (λ ps, _)),
    simp only [and_or_distrib_left, query_seed.to_query_count_seed_queries, vector.to_list_length,
      finset.sep_def, finset.mem_union, query_count.mem_active_oracles_increment_iff, ne.def,
      query_count.apply_eq_zero_iff, not_not, finset.mem_filter, list.mem_cons_iff],
    have : j ∈ qc.active_oracles ∧ ps = j ↔ ps ∈ qc.active_oracles ∧ ps = j :=
      ⟨λ hjp, ⟨hjp.2.symm ▸ hjp.1, hjp.2⟩, λ hjp, ⟨hjp.2 ▸ hjp.1, hjp.2⟩⟩,
    rw [@or_comm (j ∈ qc.active_oracles ∧ j = ps), or_assoc, @eq_comm _ j, this] }
end

lemma active_oracles_subset_of_mem_support_generate_seed_aux {qc seed js}
  (qs : query_seed spec) (hqs : qs ∈ (generate_seed_aux qc seed js).support) :
  seed.active_oracles ⊆ qs.active_oracles :=
(active_oracles_of_mem_support_generate_seed_aux qs hqs).symm ▸ finset.subset_union_left _ _


lemma to_query_count_of_mem_support_generate_seed_aux {qc seed js}
  (qs : query_seed spec) (hqs : qs ∈ (generate_seed_aux qc seed js).support) :
  qs.to_query_count = seed.to_query_count + ((js.map (λ i, query_count.of_nat)).sum) :=
begin
  induction js with j js hj generalizing seed,
  { rw [generate_seed_aux_nil, mem_support_return_iff] at hqs,
    simp [hqs] },
  {
    -- rw [generate_seed_aux_cons] at hqs,
    simp at hqs,
    obtain ⟨ps, hps⟩ := hqs,
    -- specialize hj hps,
    refine (hj hps).trans _,
    simp only [list.mem_cons_eq, query_seed.to_query_count_seed_queries],
    ext i,
    by_cases hi : i = j,
    {
      induction hi,
      simp,
    }
  }
end

end generate_seed_aux

/-- Given a count of queries `qc`, and an initial `query_store` seed, generate more outputs at
random until the number of seeded outputs for each oracle is at least the value given in `qc`. -/
noncomputable def generate_seed (qc : query_count spec) :
  oracle_comp uniform_selecting (query_seed spec) :=
generate_seed_aux qc ∅ qc.active_oracles.to_list

lemma active_oracles_of_mem_support_generate_seed (qs : query_seed spec)
  (hqs : qs ∈ (generate_seed qc).support) : qs.active_oracles = qc.active_oracles :=
by simp [active_oracles_of_mem_support_generate_seed_aux qs hqs]

@[simp] lemma mem_support_generate_seed_iff :
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