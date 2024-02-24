/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.logging_oracle
import computational_monads.simulation_semantics.constructions.seeded_oracle
import computational_monads.simulation_semantics.constructions.uniform_oracle
import computational_monads.distribution_semantics.option
import crypto_foundations.sec_experiment

/-!
# Forking Computations at a Query

Taking a computation and getting two related results from it

-/

open_locale big_operators ennreal
open oracle_comp oracle_spec fintype

variables {α β γ : Type} {spec : oracle_spec} {i : spec.ι} {q : ℕ}

section to_move

lemma prob_event_comp_congr {oa : oracle_comp spec α} {p : α → Prop}
  {ob : oracle_comp spec β} {q : β → Prop}
  (f : α → β) (hf : ∀ x ∈ oa.support, p x ↔ q (f x)) (hf' : f <$> oa ≃ₚ ob)
  : ⁅p | oa⁆ = ⁅q | ob⁆ :=
begin
  refine trans _ (hf'.prob_event_eq q),
  rw [prob_event_map],
  exact prob_event_ext' hf
end

lemma prob_event_and_le_left (oa : oracle_comp spec α) (p q : α → Prop) :
  ⁅λ x, p x ∧ q x | oa⁆ ≤ ⁅p | oa⁆ := prob_event_mono' (λ x _, and.left)

lemma prob_event_and_le_right (oa : oracle_comp spec α) (p q : α → Prop) :
  ⁅λ x, p x ∧ q x | oa⁆ ≤ ⁅q | oa⁆ := prob_event_mono' (λ x _, and.right)

lemma prob_event_id (oa : oracle_comp spec α) (p : α → Prop) :
  ⁅id | p <$> oa⁆ = ⁅p | oa⁆ := prob_event_map oa p id

lemma prob_event_eq_prob_output_true
  (oa : oracle_comp spec α) (f : α → Prop) : ⁅f | oa⁆ = ⁅= true | f <$> oa⁆ :=
by simp [← prob_event_eq_eq_prob_output]

lemma prob_event_eq_seq_map_prod_mk (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (f : α → γ) (g : β → γ) :
  ⁅λ z : α × β, f z.1 = g z.2 | prod.mk <$> oa <*> ob⁆ =
    ⁅λ z : γ × γ, z.1 = z.2 | prod.mk <$> (f <$> oa) <*> (g <$> ob)⁆ :=
by simp [prob_event_eq_prob_output_true, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

end to_move



structure fork_adversary (spec : oracle_spec) (α β : Type)
  (i : spec.ι) (q : ℕ) extends sec_adv spec α β :=
(cf : α → β → option (fin (q + 1)))
(q_lt_get_count : q < run_qb.get_count i)

namespace fork_adversary

noncomputable def advantage (adv : fork_adversary spec α β i q)
  (inp_gen : oracle_comp spec α) : ℝ≥0∞ :=
⁅(≠) none | do {x ← inp_gen, y ← adv.run x, return (adv.cf x y)}⁆

section seed_and_run

variable [is_sub_spec unif_spec spec]

noncomputable def seed_and_run (adv : fork_adversary spec α β i q) (x : α)
  (init_seed : spec.query_seed) : oracle_comp spec (β × spec.query_seed) :=
do { fresh_seed ← generate_seed (adv.run_qb - init_seed),
  z ← simulate' seededₛₒ (adv.run x) (init_seed + fresh_seed),
  return (z, (init_seed + fresh_seed)) }

variables (adv : fork_adversary spec α β i q) (x : α)

lemma seed_and_run_empty : adv.seed_and_run x ∅ = do {seed ← generate_seed adv.run_qb,
  z ← simulate' seededₛₒ (adv.run x) seed, return (z, seed)} := by simp [seed_and_run]

lemma to_query_count_of_mem_support_seed_and_run {qs qs' : spec.query_seed} {y : β}
  (h : (y, qs') ∈ (adv.seed_and_run x qs).support) (h' : ↑qs ≤ adv.run_qb) :
  qs'.to_query_count = adv.run_qb :=
begin
  simp only [seed_and_run, indexed_list.coe_query_count_eq, support_bind, support_coe_sub_spec,
    support_generate_seed, set.mem_set_of_eq, support_bind_return, support_simulate',
    set.mem_Union, set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right,
    prod.mk.inj_iff, exists_prop] at h,
  obtain ⟨qs'', h, ⟨y, ⟨hy, rfl, rfl⟩⟩⟩ := h,
  simp [h],
  refine add_tsub_cancel_of_le h',
end

lemma le_of_mem_support_seed_and_run {qs qs' : spec.query_seed} {y : β}
  (h : (y, qs') ∈ (adv.seed_and_run x qs).support) : qs ≤ qs' :=
begin
  simp only [seed_and_run, indexed_list.coe_query_count_eq, support_bind, support_coe_sub_spec,
    support_generate_seed,
  set.mem_set_of_eq, support_bind_return, support_simulate', set.mem_Union, set.mem_image, prod.exists,
  exists_and_distrib_right, exists_eq_right, prod.mk.inj_iff, exists_prop] at h,
  obtain ⟨qs'', _, _, _, _, h⟩ := h,
  refine le_of_le_of_eq (indexed_list.le_self_add _ _) h,
end

lemma lt_of_mem_support_seed_and_run (qs qs' : spec.query_seed) (y : β)
  (h : (y, qs') ∈ (adv.seed_and_run x qs).support)
  (hqs : ↑qs < adv.run_qb) : qs < qs' :=
begin
  refine lt_of_le_of_ne (le_of_mem_support_seed_and_run _ _ h) (λ h', _),
  have := to_query_count_of_mem_support_seed_and_run adv x h (le_of_lt hqs),
  rwa [h', ← this, indexed_list.coe_query_count_eq, lt_self_iff_false] at hqs,
end

lemma support_seed_and_run (qs : spec.query_seed) (hqs : ↑qs ≤ adv.run_qb) :
  (adv.seed_and_run x qs).support = {z | z.1 ∈ (simulate' seededₛₒ (adv.run x) z.2).support
      ∧ qs ≤ z.2 ∧ z.2.to_query_count = adv.run_qb} :=
begin
  rw [seed_and_run],
  simp only [set.ext_iff, ←and_assoc, indexed_list.coe_query_count_eq, support_bind,
    support_coe_sub_spec, support_generate_seed, set.mem_set_of_eq, support_bind_return,
    support_simulate', set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right,
    set.mem_Union, exists_prop, prod.forall, prod.mk.inj_iff],
  intros y qs',
  refine ⟨λ h, _, λ h, _⟩,
  {
    obtain ⟨fs, ⟨h1, h2⟩, rfl⟩ := h,
    simp [h1, h2],
    -- split,
    -- {
    --   obtain ⟨fs', hfs'⟩ := h2,
    --   have : fs' = qs + fs := by {}
    --   rw [this] at hfs',
    --   exact hfs',
    -- },
    refine add_tsub_cancel_of_le hqs,
  },
  {
    obtain ⟨⟨h, h1⟩, h2⟩ := h,
    obtain ⟨il, rfl⟩ := indexed_list.exists_eq_add_of_le h1,
    refine ⟨il, ⟨_, h⟩, rfl⟩,
    -- refine ⟨il, ⟨_, ⟨_, h⟩⟩, rfl⟩,
    rw [indexed_list.to_query_count_add] at h2,
    refine eq_tsub_of_add_eq (trans (add_comm _ _) h2),
  }
end

lemma fst_map_seed_and_run_dist_equiv (qc : spec.query_count) :
  (do {qs ← ↑(generate_seed qc), prod.fst <$> adv.seed_and_run x qs}) ≃ₚ adv.run x :=
calc (do {qs ← ↑(generate_seed qc), prod.fst <$> adv.seed_and_run x qs}) ≃ₚ
  (do {qs ← ↑(generate_seed qc), qs' ← ↑(generate_seed (adv.run_qb - qc)),
    simulate' seededₛₒ (adv.run x) (qs + qs')}) : begin
      simp [seed_and_run],
      pairwise_dist_equiv 1 with qs hqs,
      rw [support_coe_sub_spec] at hqs,
      rw [to_query_count_of_mem_support_generate_seed hqs],
    end
  ... ≃ₚ (do {qs ← ↑((+) <$> generate_seed qc <*> generate_seed (adv.run_qb - qc)),
    simulate' seededₛₒ (adv.run x) qs}) :
      begin
        simp [map_eq_bind_pure_comp, seq_eq_bind_map, bind_assoc],
      end
  ... ≃ₚ adv.run x : begin
    have := (generate_seed_add_dist_equiv qc (adv.run_qb - qc)).symm,
    rw [← coe_sub_spec_inj_dist_equiv unif_spec spec] at this,
    rw_dist_equiv [this],
    rw_dist_equiv [seeded_oracle.generate_seed_bind_simulate'_dist_equiv],
  end

lemma nth_map_seed_and_run' (init_seed : spec.query_seed) (j : spec.ι) (s : ℕ)
  (hs : s < adv.run_qb.get_count j) :
  (λ z : β × spec.query_seed, (z.2 j).nth s) <$> (adv.seed_and_run x init_seed) ≃ₚ
    if s < init_seed.get_count j then return ((init_seed j).nth s) else some <$> $ᵗ _ :=
begin
  rw [seed_and_run],
  simp only [map_bind, map_return],
  rw_dist_equiv [bind_const_dist_equiv],
  rw [← oracle_comp.map_eq_bind_return_comp, ← coe_sub_spec_map, coe_sub_spec_dist_equiv_iff],
  split_ifs with h,

  {
    -- simp only [list.nth_eq_none_iff, not_le] at h,
    simp only [list.nth_append h, indexed_list.add_apply, map_const_dist_equiv_iff],
  },
  {
    -- simp only [list.nth_eq_none_iff] at h,
    rw [not_lt] at h,
    simp only [list.nth_append_right h, indexed_list.add_apply, indexed_list.coe_query_count_eq],
    refine trans (map_nth_generate_seed_dist_equiv _ _ _) _,
    refine dist_equiv_of_eq (if_pos _),
    erw [tsub_lt_iff_left h, query_count.get_count_sub],
    simp only [indexed_list.get_count_eq_length_apply, indexed_list.apply_to_query_count, list.length_replicate],
    rw [add_tsub_cancel_of_le],
    exact hs,
    refine le_trans h (le_of_lt hs),
  },
end

lemma nth_map_seed_and_run (qs : spec.query_seed) (j : spec.ι) (s : ℕ)
  (hqs : qs.get_count j ≤ s) (hs : s < adv.run_qb.get_count j) :
  (λ z : β × spec.query_seed, (z.2 j).nth s) <$> adv.seed_and_run x qs ≃ₚ some <$> $ᵗ _ :=
begin
  refine trans (nth_map_seed_and_run' adv x qs j s hs) _,
  simp [hqs, lt_iff_not_le],
end

open prod

end seed_and_run

end fork_adversary

namespace oracle_comp

@[derive decidable_eq]
structure fork_result (adv : fork_adversary spec α β i q) :=
(fp : fin q.succ)
(out₁ : β) (out₂ : β)
(seed₁ : spec.query_seed)
(seed₂ : spec.query_seed)

variable [is_sub_spec unif_spec spec]

noncomputable def fork (adv : fork_adversary spec α β i q) :
  sec_adv spec α (option (fork_result adv)) :=
{ run := λ x, do
  { s ←$[0..q], -- choose the forking point
    init_seed ← generate_seed (adv.run_qb.take_at_index i s),
    ⟨y₁, seed₁⟩ ← adv.seed_and_run x init_seed,
    ⟨y₂, seed₂⟩ ← adv.seed_and_run x init_seed,
    -- Only return a value on success
    if adv.cf x y₁ = some s ∧ adv.cf x y₂ = some s ∧
        indexed_list.value_differs seed₁ seed₂ i s
      then return (some ⟨s, y₁, y₂, seed₁, seed₂⟩)
      else return none },
  run_qb := 2 • adv.run_qb }

variable (adv : fork_adversary spec α β i q)

lemma fork.run_eq (x : α) : (fork adv).run x = do
  { s ←$[0..q], shared_seed ← generate_seed (adv.run_qb.take_at_index i s),
    z₁ ← adv.seed_and_run x shared_seed, z₂ ← adv.seed_and_run x shared_seed,
    if adv.cf x z₁.1 = some s ∧ adv.cf x z₂.1 = some s ∧
        indexed_list.value_differs z₁.2 z₂.2 i s
      then return (some ⟨s, z₁.1, z₂.1, z₁.2, z₂.2⟩)
      else return none } :=
begin
  refine (bind_ext_congr (λ x, bind_ext_congr (λ ss, bind_ext_congr (λ z₁, _)))),
  cases z₁,
  refine bind_ext_congr (λ z₂, by cases z₂; refl)
end

@[simp] lemma fork.run_qb_eq : (fork adv).run_qb = 2 • adv.run_qb := rfl

section support

lemma indexed_list.take_at_index_add_eq_left {τ : spec.ι → Type} {il il' : spec.indexed_list τ}
  {i : spec.ι} {n : ℕ} (h : ∀ j ∈ il'.active_oracles, i = j) (hn : il.get_count i = n) :
  (il + il').take_at_index i n = il :=
begin
  refine fun_like.ext _ _ (λ j, _),
  by_cases hj : i = j,
  {
    induction hj,
    simp only [list.take_append_of_le_length (le_of_eq hn.symm), indexed_list.take_at_index_apply,
      eq_self_iff_true, indexed_list.add_apply, if_true],
    refine hn ▸ (list.take_length (il i)), 
  },
  {
    have : il' j = [] := indexed_list.apply_eq_nil (λ h', hj (h j h')),
    simp only [hj, indexed_list.take_at_index_apply, indexed_list.add_apply, if_false, this,
      list.append_nil],
  }
end

/-- Fully characterize the successful outputs of `fork`. -/
lemma some_mem_support_run_fork_iff (fr : fork_result adv) (x : α) :
  some fr ∈ ((fork adv).run x).support ↔
    (fr.out₁ ∈ (simulate' seededₛₒ (adv.run x) fr.seed₁).support ∧
      fr.out₂ ∈ (simulate' seededₛₒ (adv.run x) fr.seed₂).support) ∧
    (fr.seed₁.to_query_count = adv.run_qb ∧ fr.seed₂.to_query_count = adv.run_qb) ∧
    (fr.seed₁.take_at_index i fr.fp = fr.seed₂.take_at_index i fr.fp) ∧
    (adv.cf x fr.out₁ = some fr.fp ∧ adv.cf x fr.out₂ = some fr.fp) ∧
    (indexed_list.value_differs fr.seed₁ fr.seed₂ i fr.fp) :=
begin
  cases fr with fp out₁ out₂ seed₁ seed₂,
  simp only [fork.run_eq, ← and_assoc, -set.sep_and,
    support_bind, support_coe_sub_spec, support_uniform_fin, set.top_eq_univ, set.mem_univ,
    support_generate_seed, set.mem_set_of_eq, support_bind_ite_return, set.Union_true, set.mem_Union, set.mem_union,
    set.mem_image, set.mem_sep_iff, prod.exists, exists_eq_right, exists_and_distrib_right, and_false, exists_false,
    or_false, exists_prop, support_simulate', and.congr_left_iff],
  simp only [and_assoc],
  intros h1 h2 h3,
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨qs, hqs, ho1, ho2⟩ := h,
    have : ↑qs ≤ adv.run_qb := by simp [hqs],
    simp only [adv.support_seed_and_run x qs this,
      set.mem_set_of_eq, mem_support_simulate'_iff_exists_state] at ho1 ho2,
    refine ⟨ho1.1, ho2.1, ho1.2.2, ho2.2.2, _⟩,
    obtain ⟨qs1, rfl⟩ := indexed_list.exists_eq_add_of_le ho1.2.1,
    obtain ⟨qs2, rfl⟩ := indexed_list.exists_eq_add_of_le ho2.2.1,
    rw [indexed_list.to_query_count_add, hqs] at ho1 ho2,
    simp only [fun_like.ext_iff, indexed_list.add_apply,
      indexed_list.take_at_index_apply] at ho1 ho2,
    have hfp : qs.get_count i = ↑fp := begin
      rw [← indexed_list.get_count_to_query_count, hqs,
        indexed_list.get_count_take_at_index],
      simp only [list.length, eq_self_iff_true, if_true, min_eq_left_iff],
      refine le_trans (fin.is_le fp) (le_of_lt adv.q_lt_get_count),
    end,
    rw [indexed_list.take_at_index_add_eq_left _ hfp, indexed_list.take_at_index_add_eq_left _ hfp],
    {
      refine λ j, not_imp_not.1 (λ hij, _),
      have := ho2.2.2 j,
      rw [if_neg hij] at this,
      have := list.append_left_cancel (trans this (list.append_nil _).symm),
      rw [indexed_list.to_query_count, indexed_list.map_apply, list.map_eq_nil,
        indexed_list.apply_eq_nil_iff] at this,
      exact this,
    },
    {
      refine λ j, not_imp_not.1 (λ hij, _),
      have := ho1.2.2 j,
      rw [if_neg hij] at this,
      have := list.append_left_cancel (trans this (list.append_nil _).symm),
      rw [indexed_list.to_query_count, indexed_list.map_apply, list.map_eq_nil,
        indexed_list.apply_eq_nil_iff] at this,
      exact this,
    },

  },
  { obtain ⟨h4, h5, h6, h7, h8⟩ := h,
    have h9 : (indexed_list.take_at_index seed₁ i ↑fp) ≤ seed₂,
    by simp only [h8, indexed_list.take_at_index_le],
    have : ↑(indexed_list.take_at_index seed₁ i ↑fp) ≤ adv.run_qb,
    from le_trans (query_count.to_query_count_mono h9) (le_of_eq h7),
    refine ⟨indexed_list.take_at_index seed₁ i ↑fp, _⟩,
    simp only [adv.support_seed_and_run x _ this, h6, h7, h9, h4, h5,
      indexed_list.to_query_count_take_at_index, eq_self_iff_true, support_simulate',
      set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right, set.mem_set_of_eq,
      indexed_list.take_at_index_le, and_self] }
end

end support

section success_bound

lemma prob_event_is_some_run_fork_b (x : α) : ⁅λ fr, fr.is_some | (fork adv).run x⁆ =
  (q + 1)⁻¹ * (∑ s : fin (q + 1), let qc := (adv.run_qb.take_at_index i s) in
    ((possible_outcomes qc)⁻¹ * ∑ qs in (generate_seed qc).fin_support,
      ⁅λ z : (β × spec.query_seed) × (β × spec.query_seed),
        adv.cf x z.1.1 = some s ∧ adv.cf x z.2.1 = some s ∧
        indexed_list.value_differs z.1.2 z.2.2 i s |
          prod.mk <$> adv.seed_and_run x qs <*> adv.seed_and_run x qs⁆)) :=
begin
  simp only [fork.run_eq],
  rw [prob_event_bind_eq_sum_fintype],
  simp only [prob_output_coe_sub_spec, prob_output_uniform_fin, div_eq_mul_inv,
    finset.mul_sum, nat.cast_add, nat.cast_one],
  refine finset.sum_congr rfl (λ s hs, _),
  rw [prob_event_bind_eq_sum, fin_support_coe_sub_spec, finset.mul_sum],
  refine finset.sum_congr rfl (λ qs hqs, _),
  replace hqs := coe_of_mem_fin_support_generate_seed hqs,
  congr' 1,
  simp only [prob_output_coe_sub_spec],
  rw [prob_output_generate_seed _ _ hqs],
  congr' 1,
  rw [prob_event_eq_eq_prob_output_map],
  simp only [map_bind, apply_ite ((<$>) option.is_some),
    map_return, option.is_some_some, option.is_some_none],
  simp [prob_event_bind_eq_tsum, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left],
end



lemma prob_event_is_some_run_fork'' (x : α) :
  let h := fintype.card (spec.range i) in
  (q + 1 : ℝ≥0∞)⁻¹ * (∑ s : fin (q + 1), let qc := (adv.run_qb.take_at_index i s) in
    (possible_outcomes qc)⁻¹ * ∑ qs in (generate_seed qc).fin_support,
      (⁅λ z, adv.cf x z = some s | prod.fst <$> adv.seed_and_run x qs⁆ ^ 2 - h⁻¹) : ℝ≥0∞)
    ≤ ⁅λ fr, fr.is_some | (fork adv).run x⁆ :=
begin
  haveI : decidable_eq β := classical.dec_eq β,
  rw [prob_event_is_some_run_fork_b],
  refine mul_le_mul_left' _ _,
  refine finset.sum_le_sum (λ s hs, _),
  simp_rw [finset.mul_sum],
  refine finset.sum_le_sum (λ qs hqs, _),
  refine mul_le_mul_left' _ _,
  simp only [←and_assoc, prob_event_eq_eq_prob_output_map,
  indexed_list.value_differs_iff_nth_ne_nth, ne.def],
  rw [prob_event_and_not_eq_sub],
  refine le_trans _ (tsub_le_tsub_left (prob_event_and_le_right _ _ _) _),
  refine tsub_le_tsub _ _,
  {
    rw [← prob_event_eq_eq_prob_output', prob_event_map, function.comp, pow_two],
    refine le_of_eq (trans (symm (prob_event_seq_map_eq_mul _ _ prod.mk
      (λ z, adv.cf x z.1 = some s ∧ adv.cf x z.2 = some s) _ _
      (λ x hx y hy, iff.rfl))) _),
    simp only [prob_event_eq_prob_output_true, map_eq_bind_pure_comp,
      seq_eq_bind_map, bind_assoc, pure_bind],
  },
  {
    have hs1 := lt_of_lt_of_le s.is_lt (nat.succ_le_of_lt adv.q_lt_get_count),
    rw [indexed_list.get_count_eq_length_apply] at hs1,
    have hs' : qs.get_count i = ↑s := begin
      have := coe_of_mem_fin_support_generate_seed hqs,
      have := congr_arg (λ qs, indexed_list.get_count qs i) this,
      simp only [indexed_list.coe_query_count_eq, indexed_list.get_count_to_query_count, indexed_list.get_count_take_at_index,
        eq_self_iff_true, if_true] at this,
      rw [min_eq_left (le_of_lt hs1)] at this,
      exact this,
    end,
    refine le_of_eq _,
    rw [prob_event_eq_seq_map_prod_mk (adv.seed_and_run x qs) (adv.seed_and_run x qs)
      (λ z, (z.2 i).nth s) (λ z, (z.2 i).nth s)],
    rw [prob_event_fst_eq_snd_eq_sum],
    simp only [prob_output_seq_map_eq_mul_of_injective2 _ _ (prod.mk_injective2),
      ← pow_two],
    have := adv.nth_map_seed_and_run x qs i s (le_of_eq hs') hs1,
    simp only [this.prob_output_eq],
    simp only [finset.card_univ, pow_two, ← mul_assoc, sum_option, prob_output_none_map_some,
      mul_zero, prob_output_some_map_some, prob_output_uniform_select_fintype,
      finset.sum_const, nsmul_eq_mul, zero_add],
    rw [ennreal.mul_inv_cancel, one_mul],
    refine nat.cast_ne_zero.2 (card_ne_zero),
    refine ennreal.nat_ne_top _,
  },
end


lemma prob_event_is_some_run_fork2' (x : α) :
  let h : ℝ≥0∞ := fintype.card (spec.range i) in
  ((q + 1)⁻¹ * ∑ s : fin (q + 1), let qc := (adv.run_qb.take_at_index i s) in
    (possible_outcomes qc)⁻¹ * ∑ qs in (generate_seed qc).fin_support,
      (⁅λ z, adv.cf x z = some s | prod.fst <$> adv.seed_and_run x qs⁆ ^ 2) : ℝ≥0∞) - h⁻¹
    ≤ ⁅λ fr, fr.is_some | (fork adv).run x⁆ :=
begin
  let h : ℝ≥0∞ := fintype.card (spec.range i),
  refine le_trans _ (prob_event_is_some_run_fork'' adv x),
  simp only [finset.mul_sum],
  -- simp only [ennreal.mul_sub],

  refine le_trans (ennreal.sub_sum_le _ _ _) _,
  refine finset.sum_le_sum (λ s hs, _),
  refine le_trans (ennreal.sub_sum_le _ _ _) _,
  refine finset.sum_le_sum (λ qs hqs, _),

  refine le_of_eq _,
  simp only [← mul_assoc],
  simp only [prob_event_eq_eq_prob_output_map, map_map_eq_map_comp, card_fin_support_generate_seed,
    finset.card_fin, nat.cast_add, algebra_map.coe_one],
  rw [ennreal.mul_sub],
  {
    -- field_simp,
    congr' 2,
    rw [mul_comm]
  },
  {
    simp [ennreal.mul_eq_top],
  }
end

theorem le_prob_event_ne_none_fork (x : α) :
  (⁅(≠) none | adv.cf x <$> adv.run x⁆ / (q + 1)) ^ 2 - (card (spec.range i))⁻¹
    ≤ ⁅(≠) none | (fork adv).run x⁆ :=
begin
  simp only [prob_event_not, prob_event_eq_eq_prob_output,
    ← prob_event_is_some_eq_one_sub_prob_output_none],
  refine le_trans _ (prob_event_is_some_run_fork2' adv x),
  refine tsub_le_tsub_right _ _,
  rw [prob_event_is_some_eq_sum],
  rw [div_eq_mul_inv, mul_pow, mul_comm],
  refine le_trans (mul_le_mul le_rfl
    (ennreal.pow_two_sum_le_sum_pow_two _ _ (λ _ _, prob_output_ne_top _ _)) zero_le' zero_le') _,
  
  rw [finset.card_univ, card_fin, nat.cast_add, algebra_map.coe_one, ← mul_assoc,
    mul_comm _ (↑q + 1 : ℝ≥0∞), pow_two, ← mul_assoc],
  have h1 : (↑q + 1 : ℝ≥0∞) ≠ 0 := by simp, 
  have h2 : (↑q + 1 : ℝ≥0∞) ≠ ⊤ := by simp, 
  rw [ennreal.mul_inv_cancel h1 h2, one_mul],
  refine mul_le_mul' le_rfl (finset.sum_le_sum (λ s hs, _)),
  simp only [],
  simp_rw [← card_fin_support_generate_seed],

  -- have := ennreal.pow_two_sum_le_sum_pow_two' ((generate_seed (indexed_list.take_at_index
  --   adv.to_sec_adv.run_qb i ↑s)).fin_support) (λ qs, ⁅λ (z : β), adv.cf x z = some s|prod.fst <$> adv.seed_and_run x qs⁆)
  --   (λ _ _, prob_event_ne_top),
  refine le_trans (le_of_eq _) (ennreal.pow_two_sum_le_sum_pow_two' _ _ (λ _ _, prob_event_ne_top)),
  refine congr_arg (λ r : ℝ≥0∞, r ^ 2) _,
  rw [← prob_event_eq_eq_prob_output', prob_event_map, function.comp],

  have := adv.fst_map_seed_and_run_dist_equiv x (indexed_list.take_at_index adv.to_sec_adv.run_qb i ↑s),
  refine trans (this.symm.prob_event_eq _) _,
  simp [prob_output_generate_seed_bind, finset.mul_sum],
end

end success_bound

end oracle_comp