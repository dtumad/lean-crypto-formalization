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
open oracle_spec oracle_spec.indexed_list oracle_spec.query_count

variables {α β γ : Type} {spec spec' : oracle_spec} {τ τ' : spec.ι → Type}

section generate_aux

def generate_aux (qc : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i)) :
  list spec.ι → oracle_comp spec' (spec.indexed_list τ)
| (j :: js) := do { ts ← vector.to_list <$> repeat (oa j) (qc.get_count j),
    ((+) (of_list ts)) <$> generate_aux js }
| [] := return ∅

variables (qc : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i))

@[simp] lemma generate_aux_nil : generate_aux qc oa [] = return ∅ := rfl

lemma generate_aux_cons (j js) : generate_aux qc oa (j :: js) =
  vector.to_list <$> repeat (oa j) (qc.get_count j) >>= λ ts,
    ((+) (of_list ts)) <$> generate_aux qc oa js := rfl

lemma generate_aux_cons_dist_equiv_drop (j js) (h : j ∉ qc.active_oracles) :
  generate_aux qc oa (j :: js) ≃ₚ generate_aux qc oa js :=
begin
  rw [generate_aux_cons, get_count_eq_zero _ h, repeat_zero],
  refine trans (bind_dist_equiv_right _ _ [] _) (trans (map_dist_equiv_of_dist_equiv
    (by simp [function.funext_iff]) rfl) (map_id_dist_equiv _)),
  simp only [support_map, vector.to_list_empty, set.nonempty.image_const, support_return,
    set.singleton_nonempty, set.mem_singleton_iff, forall_eq],
end

lemma generate_aux_perm_dist_equiv {js js' : list spec.ι} (hjs : js.nodup)
  (h : js ~ js') : generate_aux qc oa js ≃ₚ generate_aux qc oa js' :=
begin
  -- intros js js' h,
  induction h with j js js' h ih j j' js js js' js'' h1 h2 hj1 hj2 generalizing hjs,
  {
    exact dist_equiv.refl (return ∅)
  },
  {
    unfold generate_aux,
    pairwise_dist_equiv [ih (list.nodup_cons.1 hjs).2],
  },
  {
    have : j ≠ j' := sorry,
    simp [generate_aux],
    sorry,
  },
  {
    have hjs' : js'.nodup := (list.perm.nodup_iff h1).1 hjs,
    specialize hj1 hjs,
    specialize hj2 hjs',
    refine hj1.trans hj2
  }
end

lemma mem_support_generate_aux_iff (js : list spec.ι) (hjs : js.nodup) (il : spec.indexed_list τ) :
  il ∈ (generate_aux qc oa js).support ↔ (il.to_query_count = {i ∈ qc | i ∈ js} ∧
    ∀ i ∈ il.active_oracles, (il i).all₂ (∈ (oa i).support)) :=
begin
  induction js with j js h generalizing hjs il,
  {
    simp only [generate_aux_nil, support_return, set.mem_singleton_iff, eq_empty_iff,
      list.not_mem_nil, sep_false_eq_empty, active_oracles_to_query_count, iff_self_and],
    exact λ h, by simp only [h, finset.not_mem_empty, is_empty.forall_iff, implies_true_iff],
  },
  {
    -- by_cases hj : j ∈ qc.active_oracles,
    { rw [list.nodup_cons] at hjs,
      specialize h hjs.2,
      -- simp only [generate_aux_cons, mem_support_bind_iff, mem_support_map_iff],
      simp only [h, generate_aux_cons, mem_support_bind_iff, support_repeat_eq_all₂,
        set.mem_set_of_eq, support_map, set.mem_image, exists_prop, list.mem_cons_iff,
        of_list_add_eq_iff],
      refine ⟨λ hqc, _, λ hqc, _⟩,
      {

        obtain ⟨ilj, hilj, il', ⟨hil', hiloa⟩, ⟨hil, rfl⟩⟩ := hqc,
        -- have hilje : ¬ ilj.to_list.empty := sorry,
        refine ⟨_, λ i hi, _⟩,
        {
          rw [sep_or_eq_sup],

          -- rw [← add_drop_at_index_eq_self il.to_query_count j ilj.to_list.length, ← to_query_count_drop_at_index,
          --   hil', apply_to_query_count, list.take_replicate, vector.to_list_length,
          --   sep_index_eq, sup_eq_add _ _ sorry],
          sorry,


        },
        {
          -- rw [list.all₂_iff_forall],
          -- intros t ht,
          sorry,
        }
      },
      {
        sorry,
      },
    },

  }
end

theorem prob_output_generate_aux (js : list spec.ι) (hjs : js.nodup)
  (il : spec.indexed_list τ) --(hil : il ∈ (generate_aux qc oa js).support)
  (hqc : il.to_query_count = {i ∈ qc | i ∈ js}) :
  ⁅= il | generate_aux qc oa js⁆ =
    ∏ j in js.to_finset, ((il j).map $ λ t, ⁅= t | oa j⁆).prod :=
begin
  induction js with j js h generalizing hjs il hqc,
  { simpa only [generate_aux_nil, list.to_finset_nil, finset.prod_empty,
    prob_output_return_eq_one_iff, eq_empty_iff, list.not_mem_nil, sep_false_eq_empty] using hqc },
  {

    rw [list.nodup_cons] at hjs,
    have hjs' : j ∉ js.to_finset := λ hjs', (hjs.1 (list.mem_to_finset.1 hjs')).elim,
    have : (il.take_at_index j 0).to_query_count = {i ∈ qc | i ∈ js},
    by simp only [hqc, hjs.1, to_query_count_take_at_index, list.mem_cons_iff, sep_or_eq_sup,
      sep_index_eq, take_at_index_sup, take_at_index_of_list, list.take_zero, of_list_nil,
      empty_sup, take_at_index_eq_self_iff, le_zero_iff, get_count_eq_zero_iff, active_oracles_sep,
      finset.sep_def, finset.mem_filter, and_false, not_false_iff],
    have hqc' : (qc j).length = (il j).length,
    { rw [← il.get_count_eq_length_apply, ← il.get_count_to_query_count, hqc, get_count_sep],
      convert eq.symm (if_pos (list.mem_cons_self j js)) },
    specialize h hjs.2 (il.take_at_index j 0) this,

    rw [generate_aux_cons, list.to_finset_cons, finset.prod_insert hjs'],

    let g1 : spec.indexed_list τ → list (τ j) := λ il, ((il j).take (il.get_count j)),
    let g2 : spec.indexed_list τ → spec.indexed_list τ := λ il, il.take_at_index j 0,
    refine trans (prob_output_bind_map_eq_mul _ _ _ g1 g2 _ _ il) _,
    {
      sorry,
    },
    {

      intros xs jl jl',
      -- have hxs' : xs.length = (il j).length := sorry,
      simp [g1, g2, of_list_add_eq_iff],
      rw [@eq_comm _ xs, @eq_comm _ jl],
      -- simp [hxs'],
      sorry,
    },
    simp only [g1, g2, list.map, list.take, h],
    congr' 1,
    {
      rw [prob_output_to_list_map_repeat],
      simpa only [hqc', get_count_eq_length_apply, list.take_length, eq_self_iff_true],

    },
    {
      refine finset.prod_congr rfl (λ j' hj', _),
      -- refine congr_arg _ _,
      have : il.take_at_index j 0 j' = il j' := begin
        simp only [take_at_index_apply, list.take_zero, ite_eq_right_iff],
        rintro rfl,
        refine (hjs' hj').elim,
      end,
      rw [this],
    }
  }
end


end generate_aux

/-- Run a computation `oa` for each of the active oracles in the query count `qc`,
aggregating the results into an indexed list. -/
noncomputable def generate (qc : spec.query_count)
  (oa : Π (i : spec.ι), oracle_comp spec' (τ i)) : oracle_comp spec' (spec.indexed_list τ) :=
generate_aux qc oa qc.active_oracles.to_list

variables (qc : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i))

lemma mem_support_generate_iff (il : spec.indexed_list τ) : il ∈ (generate qc oa).support ↔
  (il.to_query_count = qc ∧ ∀ i ∈ il.active_oracles, (il i).all₂ (∈ (oa i).support)) :=
begin
  simp_rw [generate, mem_support_generate_aux_iff qc oa _ (finset.nodup_to_list _),
    finset.mem_to_list, qc.sep_self],
  -- rw [generate],
  -- refine increment_induction qc _ (λ i n qc hi h, _),
  -- {

  --   simp [generate_aux],
  --   exact λ h, by simp only [h, finset.not_mem_empty, is_empty.forall_iff, implies_true_iff],
  -- },
  -- {
  --   have : (generate_aux (qc.increment i n.succ) oa (insert i qc.active_oracles).to_list).support =
  --     (generate_aux (qc.increment i n.succ) oa (i :: qc.active_oracles.to_list)).support,
  --   from (generate_aux_perm_dist_equiv (qc.increment i n.succ) oa
  --     (finset.nodup_to_list _) (finset.to_list_insert hi)).support_eq,


  --   simp only [active_oracles_increment, nat.succ_ne_zero, if_false],
  --   rw [this, generate_aux],


  -- }
end

end oracle_comp