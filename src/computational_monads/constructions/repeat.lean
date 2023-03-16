/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.mem
import computational_monads.constructions.product
import computational_monads.distribution_semantics.defs.prob_event

/-!
# Repeated Independent Runs of an Oracle Computation

This file defines a construction `repeat oa n` to represent running `oa` independently `n` times,
returning the result as a `vector` of length `n`, by using induction on the input `n`.

`support_repeat_eq_all₂` shows that the possible outputs of `oa.repeat n` are exactly the
vectors such that each element in the vector are possible outputs of `oa`.
`eval_dist_repeat_apply` shows that the probability of getting a given output from `oa.repeat n`
is the product over the vector of the probabilities of getting the individual outputs from `oa`.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Repeat the computation `oa` independently `n` times to get a length `n` vector of results. -/
def repeat (oa : oracle_comp spec α) : Π (n : ℕ), oracle_comp spec (vector α n)
| 0 := return vector.nil
| (n + 1) := do { a ← oa, as ← repeat n, return (a ::ᵥ as) }

variables (oa : oracle_comp spec α) (n : ℕ) {m : ℕ} (x x' : α) (xs : vector α m)
  (xs₀ : vector α 0) (xsₛ : vector α m.succ)

lemma repeat_zero : oa.repeat 0 = return vector.nil := rfl

lemma repeat_succ : oa.repeat n.succ = do {a ← oa, as ← oa.repeat n, return (a ::ᵥ as)} := rfl

instance repeat.decidable [hoa : oa.decidable] : (oa.repeat n).decidable :=
begin
  induction n with n hn,
  { exact oracle_comp.decidable_return vector.nil },
  { haveI : decidable_eq α := decidable_eq_of_decidable oa,
    refine decidable.decidable_bind' _ _ _ _ hoa (λ _, decidable.decidable_bind' _ _ _ _ hn
      (λ _, decidable.decidable_pure' _ _ (by apply_instance))) }
end

section support

/-- The support of `oa.repeat n` is the set of vectors where every element is in `oa.support`. -/
@[simp] theorem support_repeat_eq_all₂ :
  (oa.repeat n).support = {xs | xs.to_list.all₂ (∈ oa.support)} :=
begin
  induction n with n hn,
  { exact set.ext (λ x, by simp only [list.all₂, repeat_zero, support_return, set.set_of_true,
      set.mem_singleton_iff, eq_iff_true_of_subsingleton, vector.to_list_empty, set.mem_univ]) },
  { ext xs,
    obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
    simp only [hn, vector.eq_cons_iff, repeat_succ, support_bind, support_bind_return,
      set.mem_Union, set.mem_image, set.mem_set_of_eq, vector.cons_head, vector.cons_tail,
      exists_eq_right_right, exists_prop, vector.to_list_cons, list.all₂_cons] }
end

lemma support_repeat_eq_forall : (oa.repeat n).support = {xs | ∀ x ∈ xs.to_list, x ∈ oa.support} :=
by simp_rw [support_repeat_eq_all₂, list.all₂_iff_forall]

lemma mem_support_repeat_iff_all₂ : xs ∈ (oa.repeat m).support ↔ xs.to_list.all₂ (∈ oa.support) :=
by rw [support_repeat_eq_all₂, set.mem_set_of_eq]

lemma mem_support_repeat_iff_forall :
  xs ∈ (oa.repeat m).support ↔ ∀ x ∈ xs.to_list, x ∈ oa.support :=
by rw [support_repeat_eq_forall, set.mem_set_of_eq]

@[simp] lemma support_repeat_zero : (oa.repeat 0).support = {vector.nil} :=
by rw [repeat_zero, support_return]

/-- Any empty vector is in the support of a computation that is run zero times. -/
lemma mem_support_repeat_zero : xs₀ ∈ (oa.repeat 0).support :=
by simp only [repeat_zero, support_return, set.mem_singleton_iff, eq_iff_true_of_subsingleton]

/-- The support of running a computation `n + 1` is the set of vectors where the head is in
the computation's support and the tail is in the support of running it `n` times. -/
@[simp] lemma support_repeat_succ : (oa.repeat n.succ).support =
  {xs | xs.head ∈ oa.support ∧ xs.tail ∈ (oa.repeat n).support} :=
begin
  refine set.ext (λ xs, _),
  obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
  simpa only [support_repeat_eq_all₂, set.mem_set_of_eq, vector.to_list_cons,
    vector.head_cons, vector.tail_cons, list.all₂_cons]
end

lemma support_repeat_succ_eq_Union_image : (oa.repeat n.succ).support =
  ⋃ x ∈ oa.support, (vector.cons x) '' (oa.repeat n).support :=
begin
  refine set.ext (λ xs, _),
  obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
  simp_rw [set.mem_Union, support_repeat_succ, set.mem_set_of,
    vector.head_cons, vector.tail_cons, set.mem_image],
  refine ⟨λ h, ⟨x, h.1, xs, h.2, rfl⟩, λ h, _⟩,
  obtain ⟨y, hy, ys, hys, h⟩ := h,
  rw [vector.cons_eq_cons] at h,
  refine ⟨h.1 ▸ hy, h.2 ▸ hys⟩,
end

lemma mem_support_repeat_succ_iff : xsₛ ∈ (oa.repeat m.succ).support ↔
  xsₛ.head ∈ oa.support ∧ xsₛ.tail ∈ (oa.repeat m).support :=
by rw [support_repeat_succ, set.mem_set_of_eq]

lemma cons_mem_support_repeat_succ_iff : (x ::ᵥ xs) ∈ (oa.repeat m.succ).support ↔
  x ∈ oa.support ∧ xs ∈ (oa.repeat m).support :=
by rw [mem_support_repeat_succ_iff oa, vector.head_cons, vector.tail_cons]

/-- If a vector is in the support of `oa.repeat m` then any of its members is in `oa.support`. -/
lemma mem_support_of_mem_of_support_repeat {oa : oracle_comp spec α} {x : α} {xs : vector α m}
  (hxs : xs ∈ (oa.repeat m).support) (hx : x ∈ xs.to_list) : x ∈ oa.support :=
by { rw mem_support_repeat_iff_forall at hxs, exact hxs x hx }

lemma repeat_mem_support_repeat {oa : oracle_comp spec α} {x : α} (n : ℕ) (hx : x ∈ oa.support) :
  vector.repeat x n ∈ (oa.repeat n).support :=
by { rw [mem_support_repeat_iff_forall], exact (λ y hy, (list.eq_of_mem_repeat hy).symm ▸ hx) }

end support

section fin_support

lemma mem_fin_support_repeat_iff_all₂ [oa.decidable] :
  xs ∈ (oa.repeat m).fin_support ↔ xs.to_list.all₂ (∈ oa.fin_support) :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_all₂]

lemma mem_fin_support_repeat_iff_forall [oa.decidable] :
  xs ∈ (oa.repeat m).fin_support ↔ ∀ x ∈ xs.to_list, x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_forall]

end fin_support

section eval_dist

/-- The probability of getting `xs` after `oa.repeat n` is the product of the probability
of getting each individual output, since each computation runs independently. -/
@[simp] theorem eval_dist_repeat_apply : ⁅oa.repeat m⁆ xs = (xs.map ⁅oa⁆).to_list.prod :=
begin
  induction m with m hm,
  { simp only [vector.eq_nil xs, repeat_zero oa, eval_dist_return, pmf.pure_apply,
      if_true, vector.map_nil, vector.to_list_nil, list.prod_nil, eq_self_iff_true] },
  { obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
    calc ⁅oa.repeat m.succ⁆ (x ::ᵥ xs) =
      ∑' y ys, ⁅oa⁆ y * ⁅oa.repeat m⁆ ys * set.indicator {y ::ᵥ ys} (λ _, 1) (x ::ᵥ xs) :
        by simp only [repeat_succ, eval_dist_bind_apply_eq_tsum, ← ennreal.tsum_mul_left,
          eval_dist_return_apply_eq_indicator, hm, list.map, vector.to_list_map,
          vector.to_list_cons, list.prod_cons, mul_assoc]
      ... = ⁅oa⁆ x * ⁅oa.repeat m⁆ xs * set.indicator {x ::ᵥ xs} (λ _, 1) (x ::ᵥ xs) :
        begin
          refine tsum_tsum_eq_single _ x xs (λ y hy, mul_eq_zero_of_right _ $
            set.indicator_apply_eq_zero.2 (λ h, (hy _).elim)) (λ y ys hys, mul_eq_zero_of_right _ $
            set.indicator_apply_eq_zero.2 (λ h, (hys _).elim)),
          { rw [set.mem_singleton_iff, vector.cons_eq_cons] at h,
            exact h.1.symm },
          { rw [set.mem_singleton_iff, vector.cons_eq_cons] at h,
            exact h.2.symm }
        end
      ... = ⁅oa⁆ x * ⁅oa.repeat m⁆ xs :
        by simp only [set.indicator_of_mem, set.mem_singleton, mul_one]
      ... = (vector.map ⁅oa⁆ (x ::ᵥ xs)).to_list.prod :
        by rw [vector.map_cons, vector.to_list_cons, list.prod_cons, hm] }
end

lemma eval_dist_repeat_zero' : ⁅oa.repeat 0⁆ = ⁅(return vector.nil : oracle_comp spec _)⁆ := rfl

@[simp] lemma eval_dist_repeat_zero : ⁅oa.repeat 0⁆ = pmf.pure vector.nil :=
by simp only [repeat_zero, eval_dist_return]

lemma eval_dist_repeat_zero_apply : ⁅oa.repeat 0⁆ xs₀ = 1 :=
by simp only [repeat_zero, eval_dist_return, pmf.pure_apply, eq_iff_true_of_subsingleton, if_true]

lemma eval_dist_repeat_succ' :
  ⁅oa.repeat n.succ⁆ = ⁅(λ (x : α × vector α n), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat n)⁆ :=
by rw [repeat_succ, map_eq_bind_return_comp, (prod_bind_equiv_bind_bind _ _ _).eval_dist_eq]

@[simp] lemma eval_dist_repeat_succ :
  ⁅oa.repeat n.succ⁆ = ⁅oa ×ₘ oa.repeat n⁆.map (λ x, x.1 ::ᵥ x.2) :=
(oa.eval_dist_repeat_succ' n).trans (eval_dist_map _ _)

lemma eval_dist_repeat_succ_apply :
  ⁅oa.repeat m.succ⁆ xsₛ = ⁅oa⁆ xsₛ.head * ⁅oa.repeat m⁆ xsₛ.tail :=
calc ⁅oa.repeat m.succ⁆ xsₛ = ⁅(λ (x : α × vector α m), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat m)⁆ xsₛ :
    by rw eval_dist_repeat_succ' oa m
  ... = ⁅oa ×ₘ oa.repeat m⁆ (xsₛ.head, xsₛ.tail) :
    eval_dist_map_apply_eq_single' _ _ xsₛ (xsₛ.head, xsₛ.tail) (xsₛ.cons_head_tail)
      (λ x hx hx', by rw [← hx', vector.head_cons, vector.tail_cons, prod.mk.eta])
  ... = ⁅oa⁆ xsₛ.head * ⁅oa.repeat m⁆ xsₛ.tail : by rw eval_dist_product_apply

lemma eval_dist_map_nth_repeat (i : fin m) :
  ⁅(λ xs, vector.nth xs i) <$> oa.repeat m⁆ = ⁅oa⁆ :=
begin
  induction m with m hm,
  {
    refine fin.elim0 i,
  },
  {
    rw [eval_dist_map, eval_dist_repeat_succ, pmf.map_comp],
    by_cases hi : i = 0,
    {
      simp [hi], sorry,
    },
    {
      sorry,
    }
  }
end

end eval_dist

section prob_event

lemma prob_event_succ_thing (e : set (vector α m.succ)) :
  ⁅e | oa.repeat m.succ⁆ = ∑' (x : α) (xs : vector α m), e.indicator ⁅oa.repeat m.succ⁆ (x ::ᵥ xs) :=
begin
  sorry
end

/-- After repeating a computation the probability of an event holding on any single
result is the same as the probability of the event holding after running the computation once. -/
@[simp] lemma prob_event_nth_repeat (e : set α) (i : fin m) :
  ⁅λ xs, xs.nth i ∈ e | oa.repeat m⁆ = ⁅e | oa⁆ :=
trans (by simpa only [prob_event_map])
  (prob_event_eq_of_eval_dist_eq (eval_dist_map_nth_repeat oa i) e)

@[simp] lemma prob_event_head_repeat (e : set α) :
  ⁅λ xs, xs.head ∈ e | oa.repeat m.succ⁆ = ⁅e | oa⁆ :=
calc ⁅λ xs, xs.head ∈ e | oa.repeat m.succ⁆ = ⁅λ xs, xs.nth 0 ∈ e | oa.repeat m.succ⁆ :
    by simp only [vector.nth_zero]
  ... = ⁅e | oa⁆ : prob_event_nth_repeat oa e 0

lemma prob_event_all₂ (p : α → Prop) :
  ⁅λ xs, xs.to_list.all₂ p | oa.repeat m⁆ = ⁅p | oa⁆ ^ m :=
begin
  sorry
end

end prob_event

end oracle_comp