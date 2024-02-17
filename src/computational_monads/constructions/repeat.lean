/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.mem
import computational_monads.distribution_semantics.mprod
import computational_monads.distribution_semantics.subsingleton
import computational_monads.constructions.uniform_select
import computational_monads.distribution_semantics.seq -- TODO: just a standard default import

/-!
# Repeated Independent Runs of an Oracle Computation

This file defines a construction `repeat oa n` to represent running `oa` independently `n` times,
returning the result as a `vector` of length `n`, by using induction on the input `n`.

`support_repeat_eq_all₂` shows that the possible outputs of `oa.repeat n` are exactly the
vectors such that each element in the vector are possible outputs of `oa`.
`prob_output_repeat` shows that the probability of getting a given output from `oa.repeat n`
is the product over the vector of the probabilities of getting the individual outputs from `oa`.
-/

@[simp] lemma vector.append_nil {α : Type*} {n} (v : vector α n) : v.append vector.nil = v :=
begin
  cases v,
  simp [vector.nil, vector.append],
end

@[simp] lemma vector.nil_append {α : Type*} {n} (v : vector α n) :
  (vector.nil : vector α 0).append v = ((zero_add n).symm.rec_on v : vector α (0 + n)) :=
begin
  cases v,
  simp [vector.nil, vector.append, subtype.ext_iff_val],
  induction (zero_add n).symm,
  refl,
end

namespace oracle_comp

open_locale big_operators ennreal
open oracle_spec list

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Repeat the computation `oa` independently `n` times to get a length `n` vector of results. -/
def repeat (oa : oracle_comp spec α) : ℕ → oracle_comp spec (list α)
| 0 := return []
| (n + 1) := (::) <$> oa <*> repeat n

variables (oa oa' : oracle_comp spec α) (n m : ℕ) (x x' : α) (xs xs' : list α)

@[simp] lemma repeat_zero : oa.repeat 0 = return [] := rfl

@[simp] lemma repeat_succ : oa.repeat n.succ = (::) <$> oa <*> oa.repeat n := rfl

lemma repeat_add : Π (n m : ℕ), oa.repeat (n + m) =
  (++) <$> oa.repeat n <*> oa.repeat m
| n 0 := by simp only [function.comp, list.append_nil, add_zero, repeat_zero,
  seq_pure, map_map_eq_map_comp, id_map']
| 0 (m + 1) := by simp only [map_seq, function.comp, zero_add, repeat_succ, repeat_zero, map_pure,
  oracle_comp.return_seq_eq_map, map_map_eq_map_comp, nil_append]
| (n + 1) (m + 1) := begin
  have : n + 1 + (1 + m) = (n + 1 + m).succ := by ring_nf,
  rw [add_comm m 1, this, repeat_succ, add_assoc, add_comm 1 m, repeat_add n (m + 1), repeat_succ],
  simp [function.comp, map_eq_bind_pure_comp, seq_eq_bind_map, is_lawful_monad.bind_assoc],
end

section all₂

/-- The support of `oa.repeat n` is the set of vectors where every element is in `oa.support`. -/
@[simp] lemma support_repeat_eq_all₂ : (oa.repeat n).support =
  {xs | xs.length = n ∧ xs.all₂ (∈ oa.support)} :=
begin
  induction n with n hn,
  { refine set.ext (λ x, _),
    simp only [length_eq_zero, repeat_zero, support_return, set.mem_singleton_iff,
      set.mem_set_of_eq, iff_self_and],
    refine λ h, h.symm ▸ true.intro },
  { ext xs,
    simp only [hn, repeat_succ, support_seq_map, set.mem_image2, set.mem_set_of_eq,
      exists_and_distrib_left],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨x', hx', xs', ⟨hx1, hx2⟩, rfl⟩ := h,
      simp only [hx1, hx2, hx', length, eq_self_iff_true, all₂_cons, and_self] },
    { cases xs with x xs,
      { refine false.elim (nat.succ_ne_zero n h.1.symm) },
      { rw [list.all₂_cons, length_cons, nat.succ_inj'] at h,
        refine ⟨x, h.2.1, xs, ⟨h.1, h.2.2⟩, rfl⟩ } } }
end

lemma length_of_mem_support_repeat {oa : oracle_comp spec α} {n : ℕ} {xs : list α}
  (hxs : xs ∈ (oa.repeat n).support) : xs.length = n :=
begin
  rw [support_repeat_eq_all₂] at hxs,
  exact hxs.1,
end

lemma support_repeat_eq_forall : (oa.repeat n).support =
  {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ oa.support} :=
by simp_rw [support_repeat_eq_all₂, list.all₂_iff_forall]

lemma mem_support_repeat_iff_all₂ : xs ∈ (oa.repeat m).support ↔
  xs.length = m ∧ xs.all₂ (∈ oa.support) :=
by rw [support_repeat_eq_all₂, set.mem_set_of_eq]

lemma mem_support_repeat_iff_forall : xs ∈ (oa.repeat m).support ↔
  xs.length = m ∧ ∀ x ∈ xs, x ∈ oa.support :=
by rw [support_repeat_eq_forall, set.mem_set_of_eq]

lemma mem_fin_support_repeat_iff_all₂ [decidable_eq α] :
  xs ∈ (oa.repeat m).fin_support ↔ xs.length = m ∧ xs.all₂ (∈ oa.fin_support) :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_all₂]

lemma mem_fin_support_repeat_iff_forall [decidable_eq α] :
  xs ∈ (oa.repeat m).fin_support ↔ xs.length = m ∧ ∀ x ∈ xs, x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_forall]

/-- If a vector is in the support of `oa.repeat m` then any of its members is in `oa.support`. -/
lemma mem_support_of_mem_of_support_repeat {oa : oracle_comp spec α} {x : α} {xs : list α}
  (hxs : xs ∈ (oa.repeat m).support) (hx : x ∈ xs) : x ∈ oa.support :=
begin
  rw [mem_support_repeat_iff_all₂, list.all₂_iff_forall] at hxs,
  exact hxs.2 x hx
end

lemma replicate_mem_support_repeat {oa : oracle_comp spec α} {x : α} (n : ℕ) (hx : x ∈ oa.support) :
  replicate n x ∈ (oa.repeat n).support :=
begin
  rw [mem_support_repeat_iff_all₂, list.all₂_iff_forall],
  refine ⟨length_replicate n x, _⟩,
  exact (λ y hy, (list.eq_of_mem_replicate hy).symm ▸ hx)
end

end all₂

section repeat_succ

-- /-- The support of running a computation `n + 1` is the set of vectors where the head is in
-- the computation's support and the tail is in the support of running it `n` times. -/
-- @[simp] lemma support_repeat_succ : (oa.repeat n.succ).support =
--   {xs | xs.head ∈ oa.support ∧ xs.tail ∈ (oa.repeat n).support} :=
-- begin
--   refine set.ext (λ xs, _),
--   obtain ⟨x, xs, rfl⟩ := exists_eq_cons xs,
--   simpa only [support_repeat_eq_all₂, set.mem_set_of_eq, to_list_cons,
--     head_cons, tail_cons, list.all₂_cons]
-- end

-- lemma support_repeat_succ_eq_Union_image : (oa.repeat n.succ).support =
--   ⋃ x ∈ oa.support, (cons x) '' (oa.repeat n).support :=
-- by simp only [set.ext_iff, repeat_succ, support_seq_map, set.mem_image2, exists_and_distrib_left,
--   set.mem_Union, set.mem_image, exists_prop, iff_self, forall_const]

-- lemma mem_support_repeat_succ_iff : xs ∈ (oa.repeat m.succ).support ↔
--   xs.head ∈ oa.support ∧ xs.tail ∈ (oa.repeat m).support :=
-- by rw [support_repeat_succ, set.mem_set_of_eq]

-- lemma cons_mem_support_repeat_succ_iff : (x ::ᵥ xs) ∈ (oa.repeat m.succ).support ↔
--   x ∈ oa.support ∧ xs ∈ (oa.repeat m).support :=
-- by rw [mem_support_repeat_succ_iff oa, head_cons, tail_cons]

-- @[simp] lemma prob_output_repeat_succ :
--   ⁅= xsₛ | oa.repeat m.succ⁆ = ⁅= xsₛ.head | oa⁆ * ⁅= xsₛ.tail | oa.repeat m⁆ :=
-- trans (congr_arg (prob_output _) (symm (cons_head_tail _)))
--   (prob_output_seq_map_eq_mul_of_injective2 _ _ vector.injective2_cons _ _)

end repeat_succ

section nth

/-- Taking just the `i`th index element after running `repeat oa m` is distributionally
equivalent to just running `oa` a single time (although not actually equal). -/
@[pairwise_dist_equiv] lemma map_nth_repeat_dist_equiv : Π (m i : ℕ),
  (λ xs, nth xs i) <$> oa.repeat m ≃ₚ if i < m then some <$> oa else return none
| 0 i := by simp only [nth, repeat_zero, map_pure, not_lt_zero', if_false]
| (m + 1) 0 :=
  begin
    simp [seq_map_eq_bind_bind],
    rw_dist_equiv [bind_const_dist_equiv]
  end
| (m + 1) (i + 1) :=
  begin
    simp [nat.succ_lt_succ_iff, seq_map_eq_bind_bind],
    exact map_nth_repeat_dist_equiv m i,
  end

-- @[simp] lemma prob_output_map_nth_repeat (i : ℕ) (x : α) :
--   ⁅= some x | (λ xs, nth xs i) <$> oa.repeat m⁆ = ⁅= x | oa⁆ :=
-- dist_equiv.prob_output_eq (map_nth_repeat_dist_equiv oa m i) x

-- /-- After repeating a computation the probability of an event holding on any single
-- result is the same as the probability of the event holding after running the computation once. -/
-- @[simp] lemma prob_event_nth_repeat (p : α → Prop) (i : fin m) :
--   ⁅λ xs, p (xs.nth i) | oa.repeat m⁆ = ⁅p | oa⁆ :=
-- trans (prob_event_map _ _ p).symm ((map_nth_repeat_dist_equiv oa i).prob_event_eq p)

end nth

section head

-- /-- Taking just the first element after running `repeat oa m` is distributionally
-- equivalent to just running `oa` a single time (although not actually equal). -/
-- @[pairwise_dist_equiv] lemma map_head_repeat_dist_equiv [inhabited α] (m : ℕ) :
--   head <$> oa.repeat m.succ ≃ₚ oa :=
-- calc head <$> oa.repeat m.succ ≃ₚ (λ xs, (nth xs 0).get_or_else default) <$> oa.repeat m.succ :
--   by simp only [nth_zero] ... ≃ₚ oa : by pairwise_dist_equiv

-- @[simp] lemma prob_output_map_head_repeat (m : ℕ) (x : α) :
--   ⁅= x | head <$> oa.repeat m.succ⁆ = ⁅= x | oa⁆ :=
-- dist_equiv.prob_output_eq (map_head_repeat_dist_equiv oa m) x

-- @[simp] lemma prob_event_head_repeat (p : α → Prop) :
--   ⁅λ xs, p xs.head | oa.repeat m.succ⁆ = ⁅p | oa⁆ :=
-- by simp_rw [← nth_zero, prob_event_nth_repeat]

end head

section tail

/-- Taking only the tail after running `oa.repeat m` is distributionally equivalent
running `oa` one less time (although not actually equal). -/
@[pairwise_dist_equiv] lemma map_tail_repeat_dist_equiv :
  tail <$> oa.repeat n ≃ₚ oa.repeat n.pred :=
by cases n; simp [repeat_succ, map_seq, seq_eq_bind_map, oracle_comp.bind_map, function.comp]

end tail

-- @[simp] lemma prob_output_repeat' : ⁅= xs | oa.repeat m⁆ = ∏ i : fin , ⁅= xs.nth i | oa⁆ :=
-- begin
--   induction m with m hm,
--   {
--     rw [repeat_zero],
--     simp only [prob_output_of_subsingleton, fintype.univ_of_is_empty, finset.prod_empty],
--   },
--   {
--     simp only [prob_output_repeat_succ],
--     rw [fin.prod_univ_succ, nth_zero, hm],
--     simp only [nth_tail_succ],
--   }
-- end

/-- The probability of getting `xs` after `oa.repeat n` is the product of the probability
of getting each individual output, since each computation runs independently. -/
@[simp] lemma prob_output_repeat : Π (m : ℕ) (xs : list α),
  ⁅= xs | oa.repeat m⁆ = if xs.length = m then (xs.map ⁅oa⁆).prod else 0
| 0 [] := by simp only [length, repeat_zero, prob_output_eq_one_of_subset,
    set.subset_singleton_iff, support_return, set.mem_singleton_iff, imp_self, forall_const,
    eq_self_iff_true, map_nil, prod_nil, if_true]
| 0 (x :: xs) := by simp only [length, repeat_zero, add_eq_zero_iff, nat.one_ne_zero, and_false,
    if_false, prob_output_eq_zero_iff, support_return, set.mem_singleton_iff, not_false_iff]
| (m + 1) [] := have 0 ≠ m.succ := λ h, (nat.succ_ne_zero m h.symm),
    by simp only [this, length, repeat_succ, prob_output_seq_map_eq_tsum', if_false,
      ennreal.tsum_eq_zero, mul_eq_zero, prob_output_eq_zero_iff, support_return,
      set.mem_singleton_iff, not_false_iff, or_true, implies_true_iff]
| (m + 1) (x :: xs) := by simp_rw [repeat_succ, map_cons, prod_cons,
    prob_output_seq_map_eq_mul_of_injective2 _ _ list.cons_injective2, prob_output_repeat m xs,
    mul_ite, mul_zero, length_cons, eval_dist_apply_eq_prob_output, add_left_inj]

-- @[simp] lemma prob_event_repeat (p : vector α m → Prop) :
--   ⁅p | oa.repeat m⁆ = ∑' (xs : vector α m), e.indicator (λ xs, (xs.to_list.map ⁅oa⁆).prod) xs :=
-- (prob_event_eq_tsum_indicator _ e).trans (tsum_congr (λ x,
--   by simp [set.indicator, prob_output_repeat]))

lemma repeat_dist_equiv_repeat_of_dist_equiv (h : oa ≃ₚ oa') : oa.repeat n ≃ₚ oa'.repeat n :=
begin
  induction n with n hn,
  { exact return_dist_equiv_return _ _ _ },
  { simp only [repeat_succ, seq_eq_bind_map, oracle_comp.map_eq_bind_return_comp],
    pairwise_dist_equiv [h, hn] }
end

-- @[simp] lemma repeat_succ_dist_equiv_repeat_iff :
--   oa.repeat n.succ ≃ₚ oa'.repeat n.succ ↔ oa ≃ₚ oa' :=
-- begin
--   refine ⟨λ h, _, repeat_dist_equiv_repeat_of_dist_equiv oa oa' n.succ⟩,
--   calc oa ≃ₚ head <$> oa.repeat n.succ : (map_head_repeat_dist_equiv oa n).symm
--     ... ≃ₚ head <$> oa'.repeat n.succ : map_dist_equiv_map' rfl h
--     ... ≃ₚ oa' : map_head_repeat_dist_equiv oa' n
-- end

-- @[pairwise_dist_equiv] lemma repeat_uniform_select_fintype_dist_equiv [fintype α] [inhabited α]
--   [decidable_eq α] : ($ᵗ α).repeat n.succ ≃ₚ $ᵗ (vector α n.succ) :=
-- begin
--   refine dist_equiv.ext (λ xs, _),
--   have : list.map ⁅$ᵗ α⁆ xs.to_list = list.replicate n.succ (fintype.card α)⁻¹ :=
--     trans (list.map_eq_replicate_iff.2 (λ x xs, prob_output_uniform_select_fintype α x)) (by simp),
--   rw [prob_output_repeat, prob_output_uniform_select_fintype, card_vector,
--     this, list.prod_replicate, ← ennreal.inv_pow, nat.cast_pow],
-- end

-- /-- For any output `xs` of `oa.repeat m` the probability that all elements of `xs` satisfy `p`
-- is the probability of a single output of `oa` satisfying `p` raised to the `m`. -/
-- @[simp] lemma prob_event_all₂_repeat (p : α → Prop) :
--   ⁅λ xs, xs.to_list.all₂ p | oa.repeat m⁆ = ⁅p | oa⁆ ^ m :=
-- begin
--   induction m with m hm,
--   {
--     simp,
--   },
--   {
--     rw [repeat_succ],
--   }
-- end

end oracle_comp