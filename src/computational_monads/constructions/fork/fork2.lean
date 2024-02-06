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

-- TODO: move
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



structure fork_adversary (spec : oracle_spec) (α β : Type)
  (i : spec.ι) (q : ℕ) extends sec_adv spec α β :=
(choose_fork : α → β → option (fin (q + 1)))
(q_lt_get_count : q < run_qb.get_count i)

namespace fork_adversary

noncomputable def advantage (adv : fork_adversary spec α β i q)
  (inp_gen : oracle_comp spec α) : ℝ≥0∞ :=
⁅(≠) none | do {x ← inp_gen, y ← adv.run x, return (adv.choose_fork x y)}⁆

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
  simp only [seed_and_run, indexed_list.coe_query_count_eq, support_bind, support_coe_sub_spec, support_generate_seed,
  set.mem_set_of_eq, support_bind_return, support_simulate', set.mem_Union, set.mem_image, prod.exists,
  exists_and_distrib_right, exists_eq_right, prod.mk.inj_iff, exists_prop] at h,
  obtain ⟨qs'', h, ⟨y, ⟨hy, rfl, rfl⟩⟩⟩ := h,
  simp [h],
  refine add_tsub_cancel_of_le h',
end

lemma le_of_mem_support_seed_and_run {qs qs' : spec.query_seed} {y : β}
  (h : (y, qs') ∈ (adv.seed_and_run x qs).support) : qs ≤ qs' :=
begin
  simp only [seed_and_run, indexed_list.coe_query_count_eq, support_bind, support_coe_sub_spec, support_generate_seed,
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

lemma prob_event_nth_seed_and_run_eq_eq_inv (oa : oracle_comp spec γ)
  (qs : spec.query_seed) (j : spec.ι) (s : ℕ)
  (hqs : qs.get_count j ≤ s) (hs : s < adv.run_qb.get_count j)
  (f : γ → option (spec.range j)) (hf : ∀ x ∈ oa.support, f x ≠ none) :
  ⁅λ z, ((prod.fst z).2 j).nth s = f (prod.snd z) | prod.mk <$> adv.seed_and_run x qs <*> oa⁆ =
    (fintype.card (spec.range i))⁻¹ :=
calc ⁅λ z, ((prod.fst z).2 j).nth s = f (prod.snd z) | prod.mk <$> adv.seed_and_run x qs <*> oa⁆ =
  ⁅λ z, fst z = f (snd z) | prod.mk <$> ((λ z : β × spec.query_seed, (z.2 j).nth s) <$>
      adv.seed_and_run x qs) <*> oa⁆ :
    begin
      rw [map_map_eq_map_comp, function.comp,
        @prob_event_seq_map_eq_prob_event_comp_uncurry _ _ (option (spec.range j) × γ)],
      simp only [prob_event_seq_map_eq_tsum, function.comp_app, function.uncurry_apply_pair],
    end
  ... = ⁅λ z, fst z = f (snd z) | prod.mk <$> ↑(some <$> $ᵗ (spec.range j)) <*> oa⁆ :
    begin
      pairwise_dist_equiv_deep,
      rw_dist_equiv [nth_map_seed_and_run adv x qs j s hqs hs],
      rw [dist_equiv_coe_sub_spec_iff],
    end
  ... = (fintype.card (spec.range i))⁻¹ : sorry

-- lemma mem_support_seed_and_run_iff (h : ↑init_seed ≤ adv.run_qb) (z : β × spec.query_seed) :
--   z ∈ (seed_and_run adv x init_seed).support ↔
--     (z.2.take_to_count init_seed = init_seed ∧ ↑z.2 = adv.run_qb ∧
--       z.1 ∈ (simulate' seededₛₒ (adv.run x) z.2).support) :=
-- begin

-- end

end seed_and_run

end fork_adversary

namespace oracle_comp

@[derive decidable_eq]
structure fork_result (adv : fork_adversary spec α β i q) :=
(fp : fin q.succ)
(out₁ : β)
(out₂ : β)
(seed₁ : spec.query_seed)
(seed₂ : spec.query_seed)

variable [is_sub_spec unif_spec spec]

noncomputable def fork (adv : fork_adversary spec α β i q) :
  sec_adv spec α (option (fork_result adv)) :=
{ run := λ x, do
  { s ←$[0..q],
    init_seed ← generate_seed (adv.run_qb.take_at_index i s),
    ⟨y₁, seed₁⟩ ← adv.seed_and_run x init_seed,
    ⟨y₂, seed₂⟩ ← adv.seed_and_run x init_seed,
    if adv.choose_fork x y₁ = some s ∧
        adv.choose_fork x y₂ = some s ∧
        indexed_list.value_differs seed₁ seed₂ i s
      then return (some ⟨s, y₁, y₂, seed₁, seed₂⟩)
      else return none },
  run_qb := 2 • adv.run_qb }

variable (adv : fork_adversary spec α β i q)

@[simp] lemma fork.run_eq (x : α) : (fork adv).run x = do
  { s ←$[0..q], shared_seed ← generate_seed (adv.run_qb.take_at_index i s),
    z₁ ← adv.seed_and_run x shared_seed, z₂ ← adv.seed_and_run x shared_seed,
    if adv.choose_fork x z₁.1 = some s ∧ adv.choose_fork x z₂.1 = some s ∧
        indexed_list.value_differs z₁.2 z₂.2 i s
      then return (some ⟨s, z₁.1, z₂.1, z₁.2, z₂.2⟩)
      else return none } :=
begin
  refine (bind_ext_congr (λ x, bind_ext_congr (λ ss, bind_ext_congr (λ z₁, _)))),
  cases z₁,
  refine bind_ext_congr (λ z₂, by cases z₂; refl)
end

@[simp] lemma fork.run_qb_eq : (fork adv).run_qb = 2 • adv.run_qb := rfl

-- lemma some_mem_support_run_fork_iff (fr : fork_result adv) (x : α) :
--   some fr ∈ ((fork adv).run x).support ↔
--     ((fr.out₁, fr.seed₁) ∈ (adv.seed_and_run x ∅).support ∧
--       (fr.out₂, fr.seed₂) ∈ (adv.seed_and_run x (fr.seed₁.take_at_index i fr.fp)).support) ∧
--     (adv.choose_fork x fr.out₁ = some fr.fp ∧
--       adv.choose_fork x fr.out₂ = some fr.fp) ∧
--     indexed_list.value_differs fr.seed₁ fr.seed₂ i fr.fp :=
-- begin
--   simp only [fork, support_bind, set.mem_Union, exists_prop, prod.exists,
--     support_ite, support_return],
--   refine ⟨λ h, _, λ h, _⟩,
--   { obtain ⟨y₁, seed₁, h, y₂, seed₂, h', hfr⟩ := h,
--     by_cases hys : adv.choose_fork x y₁ = adv.choose_fork x y₂ ∧
--       indexed_list.value_differs seed₁ seed₂ i ↑((adv.choose_fork x y₁).get_or_else 0),
--     { obtain ⟨hys, hd⟩ := hys,
--       rw [hys] at hd,
--       simp only [hys, hd, eq_self_iff_true, if_true, set.mem_singleton_iff, true_and] at hfr,
--       rw [eq_comm, option.map_eq_some'] at hfr,
--       obtain ⟨fp, hfp, rfl⟩ := hfr,
--       simp [hfp] at hd,
--       simpa only [hys, hfp, h, hd, true_and, eq_self_iff_true, and_true] using h' },
--     { simp only [hys, if_false, set.mem_singleton_iff] at hfr,
--       exact false.elim hfr } },
--   { rcases fr with ⟨fp, out₁, out₂, seed₁, seed₂⟩,
--     refine ⟨out₁, seed₁, h.1.1, out₂, seed₂, _⟩,
--     simp [h.2.1, h.2.2, h.1.2] }
-- end

-- lemma prob_output_some_run_fork' (fr : fork_result adv) (x : α)
--   (h : some fr ∈ ((fork adv).run x).support) :
--   let shared_seed := fr.seed₁.take_at_index i fr.fp in
--   ⁅= some fr | (fork adv).run x⁆ =
--     ⁅= shared_seed | generate_seed (adv.run_qb.decrement i fr.fp)⁆ *
--     ⁅= (fr.out₁, fr.seed₁) | adv.seed_and_run x shared_seed⁆ *
--     ⁅= (fr.out₂, fr.seed₂) | adv.seed_and_run x shared_seed⁆ :=
-- begin
--   sorry
-- end
lemma prob_event_is_some_run_fork (x : α) : ⁅λ fr, fr.is_some | (fork adv).run x⁆ =
  ∑ s : fin (q + 1), (q + 1)⁻¹ *
    let qc := (adv.run_qb.take_at_index i s) in
    (∑ qs in (generate_seed qc).fin_support,
      (possible_outcomes qc)⁻¹ * ⁅λ z : β × β × spec.query_seed × spec.query_seed,
        adv.choose_fork x z.1 = some s ∧ adv.choose_fork x z.2.1 = some s ∧
        indexed_list.value_differs z.2.2.1 z.2.2.2 i s | do
      { z₁ ← adv.seed_and_run x qs,
        z₂ ← adv.seed_and_run x qs,
        return (z₁.1, z₂.1, z₁.2, z₂.2)}⁆) :=
begin
  -- haveI : decidable_eq β := classical.dec_eq β,
  -- haveI : decidable_eq α := classical.dec_eq α,
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
  simp [prob_event_bind_eq_tsum, prob_output_bind_eq_tsum],
end

lemma prob_event_is_some_run_fork' (x : α) : ⁅λ fr, fr.is_some | (fork adv).run x⁆ =
  ∑ s : fin (q + 1), (q + 1)⁻¹ * let qc := (adv.run_qb.take_at_index i s) in
    (∑ qs in (generate_seed qc).fin_support, (possible_outcomes qc)⁻¹ *
      ⁅λ z : β × β × Prop, adv.choose_fork x z.1 = some s ∧
        adv.choose_fork x z.2.1 = some s ∧ ¬ z.2.2 |
      do { z₁ ← adv.seed_and_run x qs, z₂ ← adv.seed_and_run x qs,
        return (z₁.1, z₂.1, (z₁.2 i).nth s = (z₂.2 i).nth s)}⁆) :=
begin
  rw [prob_event_is_some_run_fork],
  refine finset.sum_congr rfl (λ s hs, _),
  congr' 1,
  refine finset.sum_congr rfl (λ qs hqs, _),
  congr' 1,
  apply prob_event_comp_congr (λ z : β × β × spec.query_seed × spec.query_seed,
    (z.1, z.2.1, ((z.2.2.1 i).nth s = (z.2.2.2 i).nth s))),
  { rintros ⟨y₁, y₂, qs₁, qs₂⟩,
    simp only [indexed_list.value_differs_iff_nth_ne_nth, iff_self, implies_true_iff]},
  { simp only [oracle_comp.map_bind, map_pure] }
end

-- lemma pow_two_prob_output_some_run_fork_le (x : α) (s : fin (q + 1))
--   (qs : spec.query_seed) :
--   ⁅= some s | (λ z, adv.choose_fork x (prod.fst z)) <$> adv.seed_and_run x qs⁆ ^ 2 ≤
--     ⁅= (some s, some s) | do {z ← adv.seed_and_run⁆  

-- lemma prob_event_of_snd_snd_unused (oa : oracle_comp spec (α × β × γ))
--   (f : α × β → Prop) : ⁅λ z : α × β × γ, f (z.1, z.2.1) | oa⁆ =
--     ⁅λ z : α × β, f z | (λ z : α × β × γ, (z.1, z.2.1)) <$> oa⁆ :=
-- by rw [prob_event_map]

-- @[simp] lemma indicator_eval_dist_apply_ne_top (oa : oracle_comp spec α)
--   (s : set α) (x : α) : set.indicator s ⁅oa⁆ x ≠ ⊤ :=
-- begin
--   simp [set.indicator, ite_eq_iff', imp_false],
-- end

-- lemma pow_two_prob_event_le [fintype α] (oa : oracle_comp spec α) (p : α → Prop) :
--   ⁅p | oa⁆ ^ 2 ≤ ⁅λ x : α × α, p x.1 ∧ p x.2 | prod.mk <$> oa <*> oa⁆ / (fintype.card α) :=
-- begin
--   haveI : decidable_eq α := classical.dec_eq α,
--   haveI : decidable_pred p := classical.dec_pred p,
--   rw [prob_event_eq_sum_fintype_ite],
--   refine le_trans (ennreal.pow_two_sum_le_sum_pow_two _ _ (by simp [ite_eq_iff', imp_false])) _,
--   rw [prob_event_seq_map_eq_mul],
-- end



-- lemma map_seq_eq_map_seq_uncurry (oa : oracle_comp spec α)

lemma prob_event_is_some_run_fork'' (x : α) :
  let h := fintype.card (spec.range i) in
  (∑ s : fin (q + 1), (q + 1)⁻¹ * let qc := (adv.run_qb.take_at_index i s) in
    ∑ qs in (generate_seed qc).fin_support, (possible_outcomes qc)⁻¹ *
      (⁅λ z, adv.choose_fork x z.1 = some s | adv.seed_and_run x qs⁆ ^ 2 - h⁻¹) : ℝ≥0∞)
    ≤ ⁅λ fr, fr.is_some | (fork adv).run x⁆ :=
begin
  haveI : decidable_eq β := classical.dec_eq β,
  rw [prob_event_is_some_run_fork'],
  refine finset.sum_le_sum (λ s hs, _),
  refine mul_le_mul_left' _ _,
  refine finset.sum_le_sum (λ qs hqs, _),
  refine mul_le_mul_left' _ _,
  simp only [←and_assoc, prob_event_eq_eq_prob_output_map],
  rw [prob_event_and_not_eq_sub],
  
  refine le_trans _ (tsub_le_tsub_left (prob_event_and_le_right _ _ _) _),
  -- simp only [← prob_event_map _ (prod.snd), map_bind, map_return],
  rw [← prob_event_id _ (prod.snd ∘ prod.snd)],
  simp only [map_seq, ← seq_map_eq_bind_bind, map_map_eq_map_comp, function.comp],
  rw [← prob_event_eq_eq_prob_output', prob_event_map, function.comp, pow_two],

  rw [],
  refine le_trans (le_of_eq (congr_arg (λ r, _ - r) _)) (tsub_le_tsub_right _ _),
  {

    rw [prob_event_seq_map_eq_prob_event_comp_uncurry],
    simp only [function.comp.left_id, function.uncurry],

    have hs1 := lt_of_lt_of_le s.is_lt (nat.succ_le_of_lt adv.q_lt_get_count),
    rw [indexed_list.get_count_eq_length_apply] at hs1,
    -- have hs'' : qs.get_count i = min ↑s (adv.run_qb)
    have hs' : qs.get_count i = ↑s := begin
      -- refine le_antisymm _ _,
      -- {
        
      -- },
      have := coe_of_mem_fin_support_generate_seed hqs,
      have := congr_arg (λ qs, indexed_list.get_count qs i) this,
      simp only [indexed_list.coe_query_count_eq, indexed_list.get_count_to_query_count, indexed_list.get_count_take_at_index,
        eq_self_iff_true, if_true] at this,
      rw [min_eq_left (le_of_lt hs1)] at this,
      exact this,
    end,

    rw [fork_adversary.prob_event_nth_seed_and_run_eq_eq_inv adv x (adv.seed_and_run x qs)
      qs i s (le_of_eq hs') hs1 (λ y, (y.2 i).nth s) _],


    simp only [ne.def, list.nth_eq_none_iff, not_le, prod.forall, ← hs'],
    intros y qs' hqs,
    -- rw [← hs'],
    have := fork_adversary.lt_of_mem_support_seed_and_run _ _ _ _ _ hqs,
    specialize this _ i,
    refine lt_of_lt_of_le _ (list.is_prefix.length_le this),
  },
  {
    refine le_of_eq _,
    refine trans (symm (prob_event_seq_map_eq_mul _ _ prod.mk
      (λ z, adv.choose_fork x z.1.1 = some s ∧ adv.choose_fork x z.2.1 = some s) _ _
      (λ x hx y hy, iff.rfl))) _,
    rw [prob_event_seq_map_eq_prob_event_comp_uncurry,
      @prob_event_seq_map_eq_prob_event_comp_uncurry _ _ (β × β × Prop)],
    simp only [function.comp, prob_event_seq_map_eq_sum, function.uncurry_apply_pair],
  }
  -- rw [prob_unus]
end

end oracle_comp