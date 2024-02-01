/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.possible_outcomes
import computational_monads.constructions.repeat
import computational_monads.distribution_semantics.algebra

/-!
# Generate an Indexed List by Running a Computation According to a Count

This file defines a function `generate` for running a computation multiple times based
on a given `query_count`, generating an indexed list of the output types.
Any result will have the same "shape" as the original count, in the sense that it coerces
back to the original count under `indexed_list.coe_query_count`.
-/

namespace oracle_comp

open_locale big_operators classical
open oracle_spec oracle_spec.indexed_list oracle_spec.query_count

variables {α β γ : Type} {spec spec' : oracle_spec} {τ τ' : spec.ι → Type}

section generate_aux

def generate_aux (qc : spec.query_count)
  (oa : Π (i : spec.ι), oracle_comp spec' (τ i)) :
  list spec.ι → oracle_comp spec' (spec.indexed_list τ)
| (j :: js) :=
  do {ts ← repeat (oa j) (qc.get_count j),
      (+) (of_list ts) <$> generate_aux js}
| [] := return ∅

variables (qc : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i))

@[simp] lemma generate_aux_nil : generate_aux qc oa [] = return ∅ := rfl

lemma generate_aux_cons (j js) : generate_aux qc oa (j :: js) =
  repeat (oa j) (qc.get_count j) >>= λ ts,
    ((+) (of_list ts)) <$> generate_aux qc oa js := by rw [generate_aux]

lemma generate_aux_cons' (j js) : generate_aux qc oa (j :: js) =
  ((+) <$> of_list <$> repeat (oa j) (qc.get_count j))
    <*> (generate_aux qc oa js) :=
by simp [generate_aux, map_eq_bind_pure_comp, seq_eq_bind_map, bind_assoc]

@[simp] lemma generate_aux_singleton (j : spec.ι) : generate_aux qc oa [j] =
  of_list <$> repeat (oa j) (qc.get_count j) :=
by simpa only [generate_aux, map_return, add_empty]

@[simp] lemma generate_aux_empty (js : list spec.ι) : generate_aux ∅ oa js = return ∅ :=
begin
  induction js with j js hjs,
  { refl },
  { rw [generate_aux_cons, get_count_empty, repeat_zero, oracle_comp.return_bind,
      of_list_nil, empty_add_eq_id, id_map, hjs] }
end

lemma generate_aux_eq_generate_aux_filter (js : list spec.ι) : generate_aux qc oa js =
  generate_aux qc oa (js.filter (∈ qc.active_oracles)) :=
begin
  induction js with j js hjs,
  { rw [list.filter_nil] },
  { by_cases hj : (∈ qc.active_oracles) j,
    { simp_rw [list.filter, hj, if_true, generate_aux_cons, hjs] },
    { simp_rw [list.filter, hj, if_false, generate_aux_cons],
      rw [get_count_eq_zero qc hj, repeat_zero,
        oracle_comp.return_bind, of_list_nil, empty_add_eq_id, id_map, hjs] } }
end

-- lemma generate_aux_eq_generate_aux_filter' (js : list spec.ι) : generate_aux qc oa js =
--   generate_aux {i ∈ qc | i ∈ js} oa (js.filter (∈ qc.active_oracles)) :=
-- begin
--   induction js with j js hjs,
--   { simp only [list.filter_nil, generate_aux_nil] },
--   { by_cases hj : (∈ qc.active_oracles) j,
--     { simp_rw [list.filter, hj, if_true, generate_aux_cons],
--       rw [get_count_sep, list.mem_cons_iff, eq_self_iff_true, true_or, if_true],
--      },
--     { simp_rw [list.filter, hj, if_false, generate_aux_cons],
--       rw [get_count_eq_zero qc hj, repeat_zero, map_return, vector.to_list_nil,
--         oracle_comp.return_bind, of_list_nil, empty_add_eq_id, id_map, hjs] } }
-- end

@[simp] lemma generate_aux_of_nat (js : list spec.ι) (j n) : generate_aux (of_nat j n) oa js =
  of_list <$> repeat (oa j) (n * js.count j) :=
begin
  induction js with j' js hjs,
  { rw [generate_aux_nil, list.count_nil, mul_zero, repeat_zero, map_return, of_list_nil] },
  { by_cases hj : j = j',
    { induction hj,
      rw [generate_aux_cons, get_count_of_nat_self, list.count_cons_self, mul_add,
        mul_one, add_comm, hjs],
      simp only [map_eq_bind_pure_comp, bind_assoc, seq_eq_bind_map, function.comp_app,
        pure_bind, vector.to_list_append, of_list_append, repeat_add] },
    { rw [generate_aux_cons, get_count_of_nat, if_neg hj, repeat_zero, list.count_cons_of_ne hj],
      simp only [hjs, map_pure, vector.to_list_empty, map_map_eq_map_comp, pure_bind, of_list_nil,
        empty_add_eq_id, function.comp.left_id] } }
end

lemma generate_aux_cons_dist_equiv_drop (j js) (h : j ∉ qc.active_oracles) :
  generate_aux qc oa (j :: js) ≃ₚ generate_aux qc oa js :=
begin
  rw [generate_aux_cons, get_count_eq_zero _ h, repeat_zero],
  simp only [←indexed_list.zero_eq_empty, zero_add_eq_id, map_pure, vector.to_list_empty,
    pure_bind, of_list_nil, id_map],
end

lemma generate_aux_perm_dist_equiv {js js' : list spec.ι} (hjs : js.nodup)
  (h : js ~ js') : generate_aux qc oa js ≃ₚ generate_aux qc oa js' :=
begin
  induction h with j js js' h ih j j' js js js' js'' h1 h2 hj1 hj2 generalizing hjs,
  { exact dist_equiv.refl (return ∅) },
  { unfold generate_aux,
    pairwise_dist_equiv [ih (list.nodup_cons.1 hjs).2] },
  { simp_rw [generate_aux_cons'],
    refine seq_seq_dist_equiv_comm _ _ _ _ (λ il hil il' hil', _),
    obtain ⟨xs, hxs, rfl⟩ := (mem_support_map_iff _ _ _).1 hil,
    obtain ⟨xs', hxs', rfl⟩ := (mem_support_map_iff _ _ _).1 hil',
    simp only [function.funext_iff, comp_add_left, add_left_inj, forall_const],
    refine indexed_list.of_list_add_of_list_comm _ xs xs',
    rw [list.nodup_cons, list.mem_cons_iff, not_or_distrib] at hjs,
    exact ne.symm hjs.1.1 },
  { exact (hj1 hjs).trans (hj2 ((list.perm.nodup_iff h1).1 hjs)) }
end

lemma get_count_eq_zero_of_mem_support_generate_aux {js : list spec.ι} {il : spec.indexed_list τ}
  (hil : il ∈ (generate_aux qc oa js).support) (i : spec.ι) (hj : i ∉ js) : il.get_count i = 0 :=
begin
  induction js with j js h generalizing il hil,
  { simp only [generate_aux_nil, support_return, set.mem_singleton_iff, eq_empty_iff] at hil,
    exact il.get_count_eq_zero (hil.symm ▸ finset.not_mem_empty i) },
  { rw [list.mem_cons_iff, not_or_distrib] at hj,
    simp [generate_aux_cons] at hil,
    obtain ⟨ks, hks, il', hil'⟩ := hil,
    simp [← hil'.2, ne.symm hj.1],
    exact (il'.get_count_eq_zero_iff i).1 (h hj.2 hil'.1) }
end

lemma to_query_count_of_mem_support_generate_aux {js : list spec.ι} (hjs : js.nodup)
  {il : spec.indexed_list τ} (hil : il ∈ (generate_aux qc oa js).support) :
  il.to_query_count = {i ∈ qc | i ∈ js} :=
begin
  induction js with j js h generalizing il,
  { simp only [generate_aux_nil, support_return, set.mem_singleton_iff, eq_empty_iff] at hil,
    simp [eq_empty_of_active_oracles_eq_empty il hil] },
  { simp_rw [generate_aux_cons, mem_support_bind_iff, mem_support_map_iff] at hil,
    simp only [support_repeat_eq_all₂, set.mem_set_of_eq, exists_prop,
      exists_exists_and_eq_and] at hil,
    rw [list.nodup_cons] at hjs,
    obtain ⟨ts, hts, il', hil', htsil⟩ := hil,
    specialize h hjs.2 hil',
    simp_rw [list.mem_cons_iff, sep_or_eq_sup, ← h, ← htsil, to_query_count_add],
    refine trans _ (sup_eq_add _ _ _).symm,
    { rw [to_query_count_of_list, sep_index_eq, add_left_inj, of_nat, apply_eq_replicate_get_count,
        of_list_inj, list.replicate_left_inj],
      exact hts.1 },
    { suffices : j ∉ il'.active_oracles,
      by by_cases hj : j ∈ qc.active_oracles; simp [hj, this],
      have : il'.active_oracles = qc.active_oracles.filter (∈ js),
      by simpa only [active_oracles_to_query_count, active_oracles_sep, finset.sep_def,
        finset.filter_congr_decidable] using congr_arg active_oracles h,
      simp only [this, finset.mem_filter, not_and_distrib, hjs.1, not_false_iff, or_true] } }
end

lemma prob_output_generate_aux {js : list spec.ι} (hjs : js.nodup)
  {il : spec.indexed_list τ} (hqc : ↑il = {i ∈ qc | i ∈ js}) :
  ⁅= il | generate_aux qc oa js⁆ = ∏ j in js.to_finset, ((il j).map ⁅oa j⁆).prod :=
begin
  rw [coe_query_count_eq] at hqc,
  induction js with j js h generalizing hjs il hqc,
  { simpa only [generate_aux_nil, list.to_finset_nil, finset.prod_empty,
    prob_output_return_eq_one_iff, eq_empty_iff, list.not_mem_nil, sep_false_eq_empty] using hqc },
  { rw [list.nodup_cons] at hjs,
    have hjs' : j ∉ js.to_finset := λ hjs', (hjs.1 (list.mem_to_finset.1 hjs')).elim,
    have : (il.take_at_index j 0).to_query_count = {i ∈ qc | i ∈ js},
    by simp only [hqc, hjs.1, to_query_count_take_at_index, list.mem_cons_iff, sep_or_eq_sup,
      sep_index_eq, take_at_index_sup, take_at_index_of_list, list.take_zero, of_list_nil,
      empty_sup, take_at_index_eq_self_iff, le_zero_iff, get_count_eq_zero_iff, active_oracles_sep,
      finset.sep_def, finset.mem_filter, and_false, not_false_iff],
    have hqc' : (qc j).length = (il j).length,
    { rw [← il.get_count_eq_length_apply, ← il.get_count_to_query_count, hqc, get_count_sep],
      convert eq.symm (if_pos (list.mem_cons_self j js)) },
    rw [generate_aux_cons, list.to_finset_cons, finset.prod_insert hjs'],
    let g1 : spec.indexed_list τ → list (τ j) := λ il, ((il j).take (il.get_count j)),
    let g2 : spec.indexed_list τ → spec.indexed_list τ := λ il, il.take_at_index j 0,
    refine trans (prob_output_bind_map_eq_mul _ _ _ g1 g2 (λ xs hxs jl hjl jl', _) il) _,
    { have hjlj : jl.get_count j = 0,
      from get_count_eq_zero_of_mem_support_generate_aux _ _ hjl j hjs.1,
      simp only [g1, g2, of_list_add_eq_iff],
      rw [@eq_comm _ xs, @eq_comm _ jl, ← drop_at_index_get_count],
      refine ⟨λ hjl', _, λ hjl', _⟩,
      { have hxj := congr_arg list.length hjl'.1,
        have hjx := congr_arg (λ il, get_count il j) hjl'.2,
        simp only [hjlj, get_count_drop_at_index, eq_self_iff_true, if_true,
          tsub_eq_zero_iff_le, list.length_take, min_eq_left_iff] at hxj hjx,
        simpa only [antisymm hjx hxj] using hjl' },
      { have hxj := congr_arg list.length hjl'.1,
        simp only [get_count_eq_length_apply, list.take_length] at hxj,
        simpa only [← hxj] using hjl' } },
    simp only [g1, g2, list.map, list.take, h hjs.2 this],
    congr' 1,
    { simp only [prob_output_map_to_list, hqc', get_count_eq_length_apply, list.take_length,
        eq_self_iff_true, prob_output_repeat, vector.to_list_mk, dite_eq_ite, if_true] },
    { refine finset.prod_congr rfl (λ j' hj', _),
      suffices : il.take_at_index j 0 j' = il j', by rw [this],
      simp only [take_at_index_apply, list.take_zero, ite_eq_right_iff],
      rintro rfl,
      exact (hjs' hj').elim } }
end

lemma support_generate_aux {js : list spec.ι} (hjs : js.nodup) : (generate_aux qc oa js).support =
  {il | ↑il = {i ∈ qc | i ∈ js} ∧ ∀ i, (il i).all₂ (∈ (oa i).support)} :=
begin
  refine set.ext (λ il, _),
  rw [set.mem_set_of_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { have hil := to_query_count_of_mem_support_generate_aux qc oa hjs h,
    refine ⟨hil, λ i, _⟩,
    rw [← prob_output_ne_zero_iff, prob_output_generate_aux qc oa hjs hil] at h,
    simp only [finset.prod_eq_zero_iff, list.mem_to_finset, list.prod_eq_zero_iff, set.not_not_mem,
      exists_prop, not_exists, list.mem_map, eval_dist_apply_eq_zero_iff, ne.def, not_and] at h,
    refine list.all₂_iff_forall.2 (λ t ht, h i _ t ht),
    have hi : i ∈ il.active_oracles := mem_active_oracles_of_mem _ ht,
    rw [← active_oracles_to_query_count, hil, mem_active_oracles_sep_iff] at hi,
    exact hi.2 },
  { simp_rw [← prob_output_ne_zero_iff, prob_output_generate_aux qc oa hjs h.1, ne.def,
      finset.prod_eq_zero_iff, not_exists, list.prod_eq_zero_iff, list.mem_map, not_exists,
      list.mem_to_finset, not_and_distrib, or_iff_not_imp_left, not_not],
    refine λ i hi t ht, prob_output_ne_zero _,
    have := list.all₂_iff_forall.1 (h.2 i) t ht,
    exact this }
end

end generate_aux

/-- Run a computation `oa` for each of the active oracles in the query count `qc`,
aggregating the results into an indexed list.
Unlike `generate_aux` this is noncomputable, as we need to extract a list from the
finite set of active oracles, which requires choice. -/
noncomputable def generate (qc : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i)) :
  oracle_comp spec' (spec.indexed_list τ) :=
generate_aux qc oa qc.active_oracles.to_list

variables (qc qc' : spec.query_count) (oa : Π (i : spec.ι), oracle_comp spec' (τ i))

@[simp] lemma generate_empty : generate ∅ oa = return ∅ :=
by simp only [generate, active_oracles_empty, finset.to_list_empty, generate_aux_nil]

@[simp] lemma generate_zero : generate 0 oa = return 0 := generate_empty oa

@[simp] lemma generate_of_nat (i n) : generate (of_nat i n) oa = of_list <$> repeat (oa i) n :=
begin
  cases n with n,
  simp_rw [of_nat_zero, generate_empty, repeat_zero, map_pure, of_list_nil],
  rw [generate, generate_aux_of_nat, finset.count_to_list, active_oracles_of_nat,
    if_neg (nat.succ_ne_zero n)],
  congr; simp only [finset.mem_singleton, eq_self_iff_true, if_true, mul_one]
end

lemma support_generate : (generate qc oa).support =
  {il | ↑il = qc ∧ ∀ i, (il i).all₂ (∈ (oa i).support)} :=
by simp only [generate, support_generate_aux qc oa (finset.nodup_to_list _),
  finset.mem_to_list, sep_self]

lemma prob_output_generate' (il : spec.indexed_list τ) : ⁅= il | generate qc oa⁆ =
  if ↑il = qc then ∏ j in il.active_oracles, ((il j).map ⁅oa j⁆).prod else 0 :=
begin
  split_ifs with h,
  { have : ↑il = {i ∈ qc | i ∈ qc.active_oracles.to_list} := by simp [h],
    rw [generate, prob_output_generate_aux qc oa (finset.nodup_to_list _) this,
      finset.to_list_to_finset, ← h, coe_query_count_eq, active_oracles_to_query_count] },
  { rw [prob_output_eq_zero_iff, support_generate, set.mem_set_of_eq, not_and_distrib],
    exact or.inl h }
end

lemma prob_output_generate (il : spec.indexed_list τ) (h : ↑il = qc) :
  ⁅= il | generate qc oa⁆ = ∏ j in il.active_oracles, ((il j).map ⁅oa j⁆).prod :=
by simp only [h, prob_output_generate', eq_self_iff_true, if_true]

@[pairwise_dist_equiv] lemma generate_add_dist_equiv :
  generate (qc + qc') oa ≃ₚ ((+) <$> generate qc oa <*> generate qc' oa) :=
begin
  refine dist_equiv.ext (λ il, _),
  rw [prob_output_generate'],
  split_ifs with hil,
  {
    have := hil,
    rw [coe_query_count_eq, to_query_count_eq_add_iff] at this,
    obtain ⟨il₁, il₂, h, h'⟩ := this,
    -- induction h,
    rw [prob_output_seq_map_add_cancel_unique _ _ _ il₁ il₂],
    {
      rw [prob_output_generate _ _ _ h'.1, prob_output_generate _ _ _ h'.2], 
      rw [← h, active_oracles_add],
      simp_rw [add_apply, list.map_append, list.prod_append, finset.prod_mul_distrib],
      congr' 1,
      {
        refine symm (finset.prod_subset _ _),
        refine finset.subset_union_left _ _,
        intros j hj hj',
        rw [apply_eq_nil hj', list.map_nil, list.prod_nil],
      },
      {
        refine symm (finset.prod_subset _ _),
        refine finset.subset_union_right _ _,
        intros j hj hj',
        rw [apply_eq_nil hj', list.map_nil, list.prod_nil],
      }
    },
    {
      exact h,
    },
    {
      intros jl hjl jl' hjl' hj,
      simp only [support_generate, coe_query_count_eq, set.mem_set_of_eq] at hjl hjl',
      have := hj.trans h.symm,
      rw [add_eq_add_iff_of_to_query_count_eq] at this,
      exact this.2,
      refine hjl.1.trans h'.1.symm
    }
  },
  {
    rw [eq_comm, prob_output_eq_zero],
    rw [support_seq_map, set.mem_image2],
    simp,
    intros jl hjl jl' hjl' h,
    rw [support_generate, set.mem_set_of_eq] at hjl hjl',
    refine (hil _).elim,
    simp [← h, ← hjl'.1, ← hjl.1],

  }
end

@[pairwise_dist_equiv] lemma generate_increment_dist_equiv (i : spec.ι) (n : ℕ) :
  generate (qc.increment i n) oa ≃ₚ (+) <$> (of_list <$> repeat (oa i) n) <*> generate qc oa :=
begin
  rw [increment_eq_of_nat_add],
  rw_dist_equiv [generate_add_dist_equiv],
  rw [generate_of_nat],
end

-- lemma generate_dist_equiv_of_mem_active_oracles (i : spec.ι)
--   (hi : i ∈ qc.active_oracles) : generate qc oa ≃ₚ
--     do {x ← oa i, il ← generate (qc.decrement i 1) oa, return (of_list [x] + il)} :=
-- begin
--   have : qc = of_nat i 1 + qc.decrement i 1 := sorry,
--   rw [this],
--   rw_dist_equiv [generate_add_dist_equiv],
--   sorry,
-- end

end oracle_comp