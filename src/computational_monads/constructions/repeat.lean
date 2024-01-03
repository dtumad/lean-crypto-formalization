/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.mem
import computational_monads.distribution_semantics.mprod
import computational_monads.distribution_semantics.subsingleton
import computational_monads.constructions.uniform_select

/-!
# Repeated Independent Runs of an Oracle Computation

This file defines a construction `repeat oa n` to represent running `oa` independently `n` times,
returning the result as a `vector` of length `n`, by using induction on the input `n`.

`support_repeat_eq_all₂` shows that the possible outputs of `oa.repeat n` are exactly the
vectors such that each element in the vector are possible outputs of `oa`.
`prob_output_repeat` shows that the probability of getting a given output from `oa.repeat n`
is the product over the vector of the probabilities of getting the individual outputs from `oa`.
-/

namespace oracle_comp

open_locale big_operators ennreal
open oracle_spec vector

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Repeat the computation `oa` independently `n` times to get a length `n` vector of results. -/
def repeat (oa : oracle_comp spec α) : Π (n : ℕ), oracle_comp spec (vector α n)
| 0 := return nil
| (n + 1) := do {a ← oa, as ← repeat n, return (a ::ᵥ as)}

variables (oa oa' : oracle_comp spec α) (n : ℕ) {m : ℕ} (x x' : α) (xs : vector α m)
  (xs₀ : vector α 0) (xsₛ : vector α m.succ) (e : set (vector α m))
  (e₀ : set (vector α 0)) (esₛ : set (vector α m.succ))

@[simp] lemma repeat_zero : oa.repeat 0 = return nil := rfl

lemma repeat_succ : oa.repeat n.succ = do {a ← oa, as ← oa.repeat n, return (a ::ᵥ as)} := rfl

section all₂

/-- The support of `oa.repeat n` is the set of vectors where every element is in `oa.support`. -/
@[simp] lemma support_repeat_eq_all₂ :
  (oa.repeat n).support = {xs | xs.to_list.all₂ (∈ oa.support)} :=
begin
  induction n with n hn,
  { exact set.ext (λ x, by simp only [list.all₂, repeat_zero, support_return, set.set_of_true,
      set.mem_singleton_iff, eq_iff_true_of_subsingleton, to_list_empty, set.mem_univ]) },
  { ext xs,
    obtain ⟨x, xs, rfl⟩ := exists_eq_cons xs,
    simp only [hn, eq_cons_iff, repeat_succ, support_bind, support_bind_return,
      set.mem_Union, set.mem_image, set.mem_set_of_eq, cons_head, cons_tail,
      exists_eq_right_right, exists_prop, to_list_cons, list.all₂_cons] }
end

lemma support_repeat_eq_forall : (oa.repeat n).support = {xs | ∀ x ∈ xs.to_list, x ∈ oa.support} :=
by simp_rw [support_repeat_eq_all₂, list.all₂_iff_forall]

lemma mem_support_repeat_iff_all₂ : xs ∈ (oa.repeat m).support ↔ xs.to_list.all₂ (∈ oa.support) :=
by rw [support_repeat_eq_all₂, set.mem_set_of_eq]

lemma mem_support_repeat_iff_forall :
  xs ∈ (oa.repeat m).support ↔ ∀ x ∈ xs.to_list, x ∈ oa.support :=
by rw [support_repeat_eq_forall, set.mem_set_of_eq]

lemma mem_fin_support_repeat_iff_all₂ [decidable_eq α] :
  xs ∈ (oa.repeat m).fin_support ↔ xs.to_list.all₂ (∈ oa.fin_support) :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_all₂]

lemma mem_fin_support_repeat_iff_forall [decidable_eq α] :
  xs ∈ (oa.repeat m).fin_support ↔ ∀ x ∈ xs.to_list, x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_forall]

/-- If a vector is in the support of `oa.repeat m` then any of its members is in `oa.support`. -/
lemma mem_support_of_mem_of_support_repeat {oa : oracle_comp spec α} {x : α} {xs : vector α m}
  (hxs : xs ∈ (oa.repeat m).support) (hx : x ∈ xs.to_list) : x ∈ oa.support :=
begin
  rw [mem_support_repeat_iff_all₂, list.all₂_iff_forall] at hxs,
  exact hxs x hx
end

lemma replicate_mem_support_repeat {oa : oracle_comp spec α} {x : α} (n : ℕ) (hx : x ∈ oa.support) :
  replicate n x ∈ (oa.repeat n).support :=
begin
  rw [mem_support_repeat_iff_all₂, list.all₂_iff_forall],
  exact (λ y hy, (list.eq_of_mem_replicate hy).symm ▸ hx)
end

/-- For any output `xs` of `oa.repeat m` the probability that all elements of `xs` satisfy `p`
is the probability of a single output of `oa` satisfying `p` raised to the `m`. -/
@[simp] lemma prob_event_all₂ (p : α → Prop) :
  ⁅λ xs, xs.to_list.all₂ p | oa.repeat m⁆ = ⁅p | oa⁆ ^ m :=
begin
  induction m with m hm,
  { simp only [pow_zero, prob_event_eq_one_iff_support_subset,
      repeat_zero, support_return, set.singleton_subset_iff], },
  { rw [pow_succ, ← hm],
    simp only [repeat_succ, prob_event_bind_eq_tsum, prob_event_bind_return],
    rw [prob_event_eq_tsum_indicator, ← ennreal.tsum_mul_right],
    refine tsum_congr (λ x, _),
    by_cases hx : p x,
    { rw [set.indicator_apply_eq_self.2 (λ h, (h hx).elim)],
      refine congr_arg ((*) ⁅= x | oa⁆) (prob_event_eq_of_mem_iff _ _ _ (λ xs, _)),
      show list.all₂ p (x ::ᵥ xs).to_list ↔ list.all₂ p xs.to_list,
      by simp [hx] },
    { simp only [set.indicator_apply_eq_zero.2 (λ h, (hx h).elim), zero_mul, mul_eq_zero,
        prob_output_eq_zero_iff, prob_event_eq_zero_iff_disjoint_support, support_repeat_eq_all₂,
        or_iff_not_imp_left, not_not],
      refine λ hx', set.disjoint_iff_forall_ne.2 (λ ys hys zs hzs, _),
      have : list.all₂ p (x ::ᵥ zs).to_list := hzs,
      rw [to_list_cons, list.all₂_cons] at this,
      refine (hx this.1).elim } }
end

end all₂

section repeat_zero

/-- Repeating a computation `0` times is equivalent to any other computation,
since the output type is `vector α 0` which is a subsingleton type. -/
lemma repeat_zero_dist_equiv (oa₀ : oracle_comp spec' (vector α 0)) :
  oa.repeat 0 ≃ₚ oa₀ := by pairwise_dist_equiv

lemma repeat_zero_dist_equiv_return :
  oa.repeat 0 ≃ₚ return' !spec! nil := by pairwise_dist_equiv

lemma support_repeat_zero : (oa.repeat 0).support = {nil} := rfl

/-- Any empty vector is in the support of a computation that is run zero times. -/
lemma mem_support_repeat_zero : xs₀ ∈ (oa.repeat 0).support :=
by simp only [support_repeat_zero, set.mem_singleton_iff, eq_iff_true_of_subsingleton]

lemma fin_support_repeat_zero : (oa.repeat 0).fin_support = {nil} := rfl

lemma mem_fin_support_repeat_zero : xs₀ ∈ (oa.repeat 0).support :=
by simp only [support_repeat_zero, set.mem_singleton_iff, eq_iff_true_of_subsingleton]

lemma eval_dist_repeat_zero : ⁅oa.repeat 0⁆ = pmf.pure nil := rfl

lemma prob_output_repeat_zero : ⁅= xs₀ | oa.repeat 0⁆ = 1 :=
prob_output_of_subsingleton _ _

lemma prob_event_repeat_zero_of_nonempty (h : e₀.nonempty) : ⁅e₀ | oa.repeat 0⁆ = 1 :=
let ⟨y, hy⟩ := h in trans ((repeat_zero_dist_equiv oa (return y)).prob_event_eq _)
  (prob_event_return_of_mem spec _ hy)

end repeat_zero

section repeat_succ

/-- The support of running a computation `n + 1` is the set of vectors where the head is in
the computation's support and the tail is in the support of running it `n` times. -/
@[simp] lemma support_repeat_succ : (oa.repeat n.succ).support =
  {xs | xs.head ∈ oa.support ∧ xs.tail ∈ (oa.repeat n).support} :=
begin
  -- simp only [repeat_succ, support_bind, support_bind_return, support_repeat_eq_all₂],
  refine set.ext (λ xs, _),
  obtain ⟨x, xs, rfl⟩ := exists_eq_cons xs,
  simpa only [support_repeat_eq_all₂, set.mem_set_of_eq, to_list_cons,
    head_cons, tail_cons, list.all₂_cons]
end

lemma support_repeat_succ_eq_Union_image : (oa.repeat n.succ).support =
  ⋃ x ∈ oa.support, (cons x) '' (oa.repeat n).support :=
begin
  refine set.ext (λ xs, _),
  obtain ⟨x, xs, rfl⟩ := exists_eq_cons xs,
  simp_rw [set.mem_Union, support_repeat_succ, set.mem_set_of,
    head_cons, tail_cons, set.mem_image],
  refine ⟨λ h, ⟨x, h.1, xs, h.2, rfl⟩, λ h, _⟩,
  obtain ⟨y, hy, ys, hys, h⟩ := h,
  rw [eq_cons_iff, head_cons, tail_cons] at h,
  refine ⟨h.1 ▸ hy, h.2 ▸ hys⟩,
end

lemma mem_support_repeat_succ_iff : xsₛ ∈ (oa.repeat m.succ).support ↔
  xsₛ.head ∈ oa.support ∧ xsₛ.tail ∈ (oa.repeat m).support :=
by rw [support_repeat_succ, set.mem_set_of_eq]

lemma cons_mem_support_repeat_succ_iff : (x ::ᵥ xs) ∈ (oa.repeat m.succ).support ↔
  x ∈ oa.support ∧ xs ∈ (oa.repeat m).support :=
by rw [mem_support_repeat_succ_iff oa, head_cons, tail_cons]

lemma repeat_succ_dist_equiv : oa.repeat n.succ ≃ₚ
  (λ (x : α × vector α n), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat n) :=
by rw [dist_equiv.def, repeat_succ, oracle_comp.map_eq_bind_return_comp,
  (mprod_bind_equiv_bind_bind _ _ _).eval_dist_eq]

lemma eval_dist_repeat_succ' : ⁅oa.repeat n.succ⁆ =
  ⁅(λ (x : α × vector α n), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat n)⁆ :=
by rw [repeat_succ, oracle_comp.map_eq_bind_return_comp, (mprod_bind_equiv_bind_bind _ _ _).eval_dist_eq]

@[simp] lemma eval_dist_repeat_succ :
  ⁅oa.repeat n.succ⁆ = ⁅oa ×ₘ oa.repeat n⁆.map (λ x, x.1 ::ᵥ x.2) :=
(oa.eval_dist_repeat_succ' n).trans (eval_dist_map _ _)

@[simp] lemma prob_output_repeat_succ :
  ⁅= xsₛ | oa.repeat m.succ⁆ = ⁅= xsₛ.head | oa⁆ * ⁅= xsₛ.tail | oa.repeat m⁆ :=
calc ⁅= xsₛ | oa.repeat m.succ⁆ =
  ⁅(λ (x : α × vector α m), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat m)⁆ xsₛ :
    by rw [prob_output.def, eval_dist_repeat_succ' oa m]
  ... = ⁅= (xsₛ.head, xsₛ.tail) | oa ×ₘ oa.repeat m⁆ :
    prob_output_map_eq_single' _ _ (xsₛ.head, xsₛ.tail) xsₛ (xsₛ.cons_head_tail)
      (λ x hx hx', by rw [← hx', head_cons, tail_cons, prod.mk.eta])
  ... = ⁅= xsₛ.head | oa⁆ * ⁅= xsₛ.tail | oa.repeat m⁆ : by rw prob_output_mprod

end repeat_succ

section map

@[pairwise_dist_equiv] lemma map_nth_repeat_dist_equiv (i : fin m) :
  (λ xs, nth xs i) <$> oa.repeat m ≃ₚ oa :=
begin
  haveI : inhabited α := ⟨oa.default_result⟩,
  induction m with m hm,
  { exact fin.elim0 i },
  { refine fin.induction_on i _ (λ i hi, _),
    { simp only [nth_zero, repeat_succ, oracle_comp.map_bind, map_pure,
        cons_head, oracle_comp.pure_eq_return],
      rw_dist_equiv [bind_const_dist_equiv, bind_return_dist_equiv] },
    { simpa only [repeat_succ, oracle_comp.map_bind, map_pure, nth_cons_succ,
        bind_const_dist_equiv_iff] using hm i} }
end

@[pairwise_dist_equiv] lemma map_head_repeat_dist_equiv (m : ℕ) :
  head <$> oa.repeat m.succ ≃ₚ oa :=
calc head <$> oa.repeat m.succ ≃ₚ (λ xs, nth xs 0) <$> oa.repeat m.succ :
  by simp only [nth_zero] ... ≃ₚ oa : by pairwise_dist_equiv

@[simp] lemma prob_output_map_nth_repeat (i : fin m) (x : α) :
  ⁅= x | (λ xs, nth xs i) <$> oa.repeat m⁆ = ⁅= x | oa⁆ :=
dist_equiv.prob_output_eq (map_nth_repeat_dist_equiv oa i) x

@[simp] lemma prob_output_map_head_repeat (m : ℕ) (x : α) :
  ⁅= x | head <$> oa.repeat m.succ⁆ = ⁅= x | oa⁆ :=
dist_equiv.prob_output_eq (map_head_repeat_dist_equiv oa m) x

/-- After repeating a computation the probability of an event holding on any single
result is the same as the probability of the event holding after running the computation once. -/
@[simp] lemma prob_event_nth_repeat (e : set α) (i : fin m) :
  ⁅λ xs, xs.nth i ∈ e | oa.repeat m⁆ = ⁅e | oa⁆ :=
trans (by simpa only [prob_event_map])
  (prob_event_eq_of_eval_dist_eq (map_nth_repeat_dist_equiv oa i) e)

@[simp] lemma prob_event_head_repeat (e : set α) :
  ⁅λ xs, xs.head ∈ e | oa.repeat m.succ⁆ = ⁅e | oa⁆ :=
calc ⁅λ xs, xs.head ∈ e | oa.repeat m.succ⁆ = ⁅λ xs, xs.nth 0 ∈ e | oa.repeat m.succ⁆ :
    by simp only [nth_zero]
  ... = ⁅e | oa⁆ : prob_event_nth_repeat oa e 0

end map

section tail

@[pairwise_dist_equiv] lemma map_tail_repeat_dist_equiv :
  tail <$> oa.repeat n ≃ₚ oa.repeat n.pred :=
begin
  induction n with n hn,
  {
    simp,
  },
  {
    rw [repeat_succ],
    simpa,
  }
end

end tail

@[simp] lemma prob_output_repeat' : ⁅= xs | oa.repeat m⁆ = ∏ i, ⁅= xs.nth i | oa⁆ :=
begin
  induction m with m hm,
  {
    rw [repeat_zero],
    simp only [prob_output_of_subsingleton, fintype.univ_of_is_empty, finset.prod_empty],
  },
  {
    simp only [prob_output_repeat_succ],
    rw [fin.prod_univ_succ, nth_zero, hm],
    simp only [nth_tail_succ],
  }
end

/-- The probability of getting `xs` after `oa.repeat n` is the product of the probability
of getting each individual output, since each computation runs independently. -/
@[simp] lemma prob_output_repeat : ⁅= xs | oa.repeat m⁆ = (xs.to_list.map ⁅oa⁆).prod :=
begin
  induction m with m hm,
  { simp only [vector.eq_nil xs, repeat_zero oa, prob_output_return,
      if_true, list.map_nil, to_list_nil, list.prod_nil, eq_self_iff_true] },
  { obtain ⟨x, xs, rfl⟩ := exists_eq_cons xs,
    calc ⁅= x ::ᵥ xs | oa.repeat m.succ⁆ =
      ∑' y ys, ⁅= y | oa⁆ * ⁅= ys | oa.repeat m⁆ * set.indicator {y ::ᵥ ys} (λ _, 1) (x ::ᵥ xs) :
        by simp only [repeat_succ, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left,
          prob_output_return_eq_indicator, hm, list.map, to_list_map,
          to_list_cons, list.prod_cons, mul_assoc]
      ... = ⁅= x | oa⁆ * ⁅= xs | oa.repeat m⁆ * set.indicator {x ::ᵥ xs} (λ _, 1) (x ::ᵥ xs) :
        begin
          refine tsum_tsum_eq_single _ x xs (λ y hy, mul_eq_zero_of_right _ $
            set.indicator_apply_eq_zero.2 (λ h, (hy _).elim)) (λ y ys hys, mul_eq_zero_of_right _ $
            set.indicator_apply_eq_zero.2 (λ h, (hys _).elim)),
          { rw [set.mem_singleton_iff, eq_cons_iff, head_cons, tail_cons] at h,
            exact h.1.symm },
          { rw [set.mem_singleton_iff, eq_cons_iff, head_cons, tail_cons] at h,
            exact h.2.symm }
        end
      ... = ⁅= x | oa⁆ * ⁅= xs | oa.repeat m⁆ :
        by simp only [set.indicator_of_mem, set.mem_singleton, mul_one]
      ... = ((x ::ᵥ xs).to_list.map ⁅oa⁆).prod :
        by rw [to_list_cons, list.map_cons, list.prod_cons, hm, eval_dist_apply_eq_prob_output] }
end

@[simp] lemma prob_event_repeat (e : set (vector α m)) :
  ⁅e | oa.repeat m⁆ = ∑' (xs : vector α m), e.indicator (λ xs, (xs.to_list.map ⁅oa⁆).prod) xs :=
(prob_event_eq_tsum_indicator _ e).trans (tsum_congr (λ x,
  by simp [set.indicator, prob_output_repeat]))

lemma repeat_dist_equiv_repeat_of_dist_equiv (h : oa ≃ₚ oa') : oa.repeat n ≃ₚ oa'.repeat n :=
begin
  induction n with n hn,
  pairwise_dist_equiv,
  simp_rw [repeat_succ],
  pairwise_dist_equiv [h, hn],
end

@[simp] lemma repeat_succ_dist_equiv_repeat_iff :
  oa.repeat n.succ ≃ₚ oa'.repeat n.succ ↔ oa ≃ₚ oa' :=
begin
  refine ⟨λ h, _, repeat_dist_equiv_repeat_of_dist_equiv oa oa' n.succ⟩,
  calc oa ≃ₚ head <$> oa.repeat n.succ : (map_head_repeat_dist_equiv oa n).symm
    ... ≃ₚ head <$> oa'.repeat n.succ : map_dist_equiv_of_dist_equiv' rfl h
    ... ≃ₚ oa' : map_head_repeat_dist_equiv oa' n
end

@[pairwise_dist_equiv] lemma repeat_uniform_select_fintype_dist_equiv [fintype α] [inhabited α]
  [decidable_eq α] : ($ᵗ α).repeat n.succ ≃ₚ $ᵗ (vector α n.succ) :=
begin
  refine dist_equiv.ext (λ xs, _),
  have : list.map ⁅$ᵗ α⁆ xs.to_list = list.replicate n.succ (fintype.card α)⁻¹ :=
    trans (list.map_eq_replicate_iff.2 (λ x xs, prob_output_uniform_select_fintype α x)) (by simp),
  rw [prob_output_repeat, prob_output_uniform_select_fintype, card_vector,
    this, list.prod_replicate, ← ennreal.inv_pow, nat.cast_pow],
end

@[simp] lemma prob_output_map_to_list (xs : list α) (oa : oracle_comp spec (vector α n)) :
  ⁅= xs | to_list <$> oa⁆ = if h : xs.length = n then ⁅= ⟨xs, h⟩ | oa⁆ else 0 :=
begin
  split_ifs with h,
  {
    exact (prob_output_map_of_injective oa
      vector.to_list ⟨xs, h⟩ vector.to_list_injective),
  },
  {
    simp_rw [prob_output_eq_zero_iff, support_map, set.mem_image, not_exists, not_and_distrib],
    refine λ xs', or.inr (λ hxs', h (hxs' ▸ xs'.to_list_length)),

  }
end

@[simp] lemma prob_output_to_list_map_repeat (xs : list α) :
  ⁅= xs | vector.to_list <$> repeat oa n⁆ = if xs.length = n then (xs.map ⁅oa⁆).prod else 0 :=
begin
  simp,
end

end oracle_comp