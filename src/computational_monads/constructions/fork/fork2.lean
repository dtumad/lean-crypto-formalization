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

structure fork_adversary (spec : oracle_spec) (α β : Type)
  (i : spec.ι) (q : ℕ) extends sec_adv spec α β :=
(choose_fork : α → β → option (fin q.succ))

namespace fork_adversary

noncomputable def advantage (adv : fork_adversary spec α β i q)
  (inp_gen : oracle_comp spec α) : ℝ≥0∞ :=
⁅(≠) none | do {x ← inp_gen, y ← adv.run x, return (adv.choose_fork x y)}⁆

section seed_and_run

variable [is_sub_spec unif_spec spec]

noncomputable def seed_and_run (adv : fork_adversary spec α β i q)
  (x : α) (init_seed : spec.query_seed) : oracle_comp spec (β × spec.query_seed) :=
do {fresh_seed ← generate_seed (adv.run_qb - init_seed),
  z ← simulate' seededₛₒ (adv.run x) (init_seed + fresh_seed),
  return (z, (init_seed + fresh_seed))}

variables (adv : fork_adversary spec α β i q)
  (x : α) (init_seed : spec.query_seed)

-- lemma mem_support_seed_and_run_iff (h : ↑init_seed ≤ adv.run_qb) (z : β × spec.query_seed) :
--   z ∈ (seed_and_run adv x init_seed).support ↔
--     (z.2.take_to_count init_seed = init_seed ∧ ↑z.2 = adv.run_qb ∧
--       z.1 ∈ (simulate' seededₛₒ (adv.run x) z.2).support) :=
-- begin

-- end

end seed_and_run

end fork_adversary

namespace oracle_comp

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
    init_seed ← generate_seed (adv.run_qb.decrement i s),
    ⟨y₁, seed₁⟩ ← adv.seed_and_run x init_seed,
    ⟨y₂, seed₂⟩ ← adv.seed_and_run x init_seed,
    if adv.choose_fork x y₁ = some s ∧
        adv.choose_fork x y₂ = some s ∧
        indexed_list.value_differs seed₁ seed₂ i s
      then return (some ⟨s, y₁, y₂, seed₁, seed₂⟩)
      else return none },
  run_qb := 2 • adv.run_qb }

variable (adv : fork_adversary spec α β i q)

@[simp] lemma fork.run_eq : (fork adv).run = λ x, do
  { s ←$[0..q], shared_seed ← generate_seed (adv.run_qb.decrement i s),
    z₁ ← adv.seed_and_run x shared_seed, z₂ ← adv.seed_and_run x shared_seed,
    if adv.choose_fork x z₁.1 = some s ∧ adv.choose_fork x z₂.1 = some s ∧
        indexed_list.value_differs z₁.2 z₂.2 i s
      then return (some ⟨s, z₁.1, z₂.1, z₁.2, z₂.2⟩)
      else return none } :=
begin
  ext x,
  refine (bind_ext_congr (λ x, bind_ext_congr (λ ss, bind_ext_congr (λ z₁, _)))),
  cases z₁,
  refine bind_ext_congr (λ z₂, by cases z₂; refl)
end

lemma fork.run_apply_eq (x : α) : (fork adv).run x = do
  { s ←$[0..q], shared_seed ← generate_seed (adv.run_qb.decrement i s),
    z₁ ← adv.seed_and_run x shared_seed, z₂ ← adv.seed_and_run x shared_seed,
    if adv.choose_fork x z₁.1 = some s ∧ adv.choose_fork x z₂.1 = some s ∧
        indexed_list.value_differs z₁.2 z₂.2 i s
      then return (some ⟨s, z₁.1, z₂.1, z₁.2, z₂.2⟩)
      else return none } := by simp only [fork.run_eq]

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

lemma prob_output_some_run_fork' (fr : fork_result adv) (x : α)
  (h : some fr ∈ ((fork adv).run x).support) :
  let shared_seed := fr.seed₁.take_at_index i fr.fp in
  ⁅= some fr | (fork adv).run x⁆ =
    ⁅= shared_seed | generate_seed (adv.run_qb.decrement i fr.fp)⁆ *
    ⁅= (fr.out₁, fr.seed₁) | adv.seed_and_run x shared_seed⁆ *
    ⁅= (fr.out₂, fr.seed₂) | adv.seed_and_run x shared_seed⁆ :=
begin
  sorry
end

lemma prob_event_is_some_fork (x : α) : ⁅λ fr, fr.is_some | (fork adv).run x⁆ =
  ∑ s : fin q, ∑ qs in (generate_seed (adv.run_qb.decrement i s)).fin_support,
    (⁅λ z : β × β × spec.query_seed × spec.query_seed,
        adv.choose_fork x z.1 = some s ∧ adv.choose_fork x z.2.1 = some s ∧
        indexed_list.value_differs z.2.2.1 z.2.2.2 i s | do
      { z₁ ← adv.seed_and_run x qs,
           z₂ ← adv.seed_and_run x qs,
           return (z₁.1, z₂.1, z₁.2, z₂.2)}⁆) / q :=
begin
  simp only [fork.run_eq],
  rw [prob_event_uniform_fin_bind_apply_eq_sum],
end

-- lemma prob_output_some_run_fork (fr : fork_result adv) (x : α) :
--   ⁅= fr | (fork adv).run x⁆ =
--     ⁅= fr.seed₁ | generate_seed adv.run_qb⁆ *
--       ⁅= fr.out₁ | simulate' seededₛₒ (adv.run x) fr.seed₁⁆ *
--       ⁅= fr.seed₂ | (λ qs, fr.seed₁.take_at_index i fr.fp) <$>
--         generate_seed (adv.run_qb - fr.seed₁)⁆ *
--       ⁅= fr.out₂ | simulate' seededₛₒ (adv.run x) fr.seed₂⁆ :=
-- begin

-- end

lemma le_prob_event_ne_none_fork (inp_gen : oracle_comp spec α) :
  let r := adv.advantage inp_gen in
  let h := fintype.card (spec.range i) in 
  r * (r / q - 1 / h) ≤ ⁅λ fr, fr.is_some | do {x ← inp_gen, (fork adv).run x}⁆ :=
calc (adv.advantage inp_gen) * (adv.advantage inp_gen / q - 1 / fintype.card (spec.range i)) ≤
  ∑ s : fin q, ∑ qs in (generate_seed (adv.run_qb.decrement i s)).fin_support,
    _: 
    begin

    end
  ... = ∑' x, ⁅= x | inp_gen⁆
  ... = ∑' x, ⁅= x | inp_gen⁆ * ⁅λ fr, fr.is_some | (fork adv).run x⁆ :
    begin

    end
  ... = ⁅λ fr, fr.is_some | do {x ← inp_gen, (fork adv).run x}⁆ :
    begin
      rw [prob_event_is_some],
    end


end oracle_comp


-- noncomputable def fork (adv : fork_adversary spec α β i q) :
--   sec_adv spec α (option (fork_result adv)) :=
-- { run := λ x, do
--   { ⟨y₁, seed₁⟩ ← adv.seed_and_run x ∅,
--     let cf := adv.choose_fork x y₁,
--     let fp := cf.get_or_else 0,
--     let qs := seed₁.take_at_index i fp,
--     ⟨y₂, seed₂⟩ ← adv.seed_and_run x qs,
--     if adv.choose_fork x y₁ = adv.choose_fork x y₂
--         ∧ indexed_list.value_differs seed₁ seed₂ i fp
--       then return (cf.map (λ fp, ⟨fp, y₁, y₂, seed₁, seed₂⟩))
--       else return none },
--   run_qb := 2 • adv.run_qb }

-- variable (adv : fork_adversary spec α β i q)

-- @[simp] lemma fork.run_eq : (fork adv).run = λ x, do
--   { z₁ ← adv.seed_and_run x ∅,
--     z₂ ← adv.seed_and_run x (z₁.2.take_at_index i ((adv.choose_fork x z₁.1).get_or_else 0)),
--     if adv.choose_fork x z₁.1 = adv.choose_fork x z₂.1
--         ∧ indexed_list.value_differs z₁.2 z₂.2 i (((adv.choose_fork x z₁.1).get_or_else 0))
--       then return ((adv.choose_fork x z₁.1).map (λ fp, ⟨fp, z₁.1, z₂.1, z₁.2, z₂.2⟩))
--       else return none } :=
-- funext (λ x, bind_ext_congr (λ z1, match z1 with
--   | ⟨_, _⟩ := bind_ext_congr (λ z2, by cases z2; refl) end))

-- @[simp] lemma fork.run_qb_eq : (fork adv).run_qb = 2 • adv.run_qb := rfl

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

-- lemma prob_output_some_run_fork' (fr : fork_result adv) (x : α) :
--   let shared_seed := fr.seed₁.take_at_index i fr.fp in
--   ⁅= fr | (fork adv).run x⁆ =
--     ⁅= fr.seed₁.take_at_index i fr.fp |
--       generate_seed (adv.run_qb.decrement i fr.fp)⁆ *
--     ⁅= (fr.out₁, fr.seed₁) | adv.seed_and_run x ⁆

-- lemma prob_output_some_run_fork (fr : fork_result adv) (x : α) :
--   ⁅= fr | (fork adv).run x⁆ =
--     ⁅= fr.seed₁ | generate_seed adv.run_qb⁆ *
--       ⁅= fr.out₁ | simulate' seededₛₒ (adv.run x) fr.seed₁⁆ *
--       ⁅= fr.seed₂ | (λ qs, fr.seed₁.take_at_index i fr.fp) <$>
--         generate_seed (adv.run_qb - fr.seed₁)⁆ *
--       ⁅= fr.out₂ | simulate' seededₛₒ (adv.run x) fr.seed₂⁆ :=
-- begin

-- end

-- lemma le_prob_event_ne_none_fork (inp_gen : oracle_comp spec α) :
--   let r := adv.advantage inp_gen in
--   let h := fintype.card (spec.range i) in 
--   r * (r / q - 1 / h) ≤ ⁅λ fr, fr.is_some | do {x ← inp_gen, (fork adv).run x}⁆ :=

-- calc (adv.advantage inp_gen) * (adv.advantage inp_gen / q - 1 / fintype.card (spec.range i)) ≤
--   ∑' x fr, ⁅= x | inp_gen⁆ * ⁅= some fr | (fork adv).run x⁆ : 
--     begin

--     end
--   ... = ⁅λ fr, fr.is_some | do {x ← inp_gen, (fork adv).run x}⁆ :
--     begin
--       rw [prob_event_is_some],
--     end