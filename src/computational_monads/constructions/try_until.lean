/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.constructions.repeat
import computational_monads.distribution_semantics.ite

/-!
# Repeated Computation Until a Condition

This file defines a construction `try_until oa p n` that repeats a computation until `p` holds.
The parameter `n` gives a bound on the number of runs (called "gas" in some formulations).
This solves the problem of an unbounded computation, by giving a finite computation depth.
Because this may not always produce a final result, we use an option type to represent failure.

We implement this as a mapping of `oracle_comp.repeat` for simplicity in deriving lemmas.
This means that the computation always "runs" `n` times even if a result is found before that.
However it isn't clear that this is commonly a problem, so we take this approach for now.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Computation that repeats `oa` until `p` holds on the result, with at most `n` attempts. -/
def try_until (oa : oracle_comp spec α) (p : α → Prop) [decidable_pred p]
  (n : ℕ) : oracle_comp spec (option α) :=
(λ xs, (vector.to_list xs).find p) <$> (repeat oa n)

variables (oa : oracle_comp spec α) (p : α → Prop) [decidable_pred p]
  (n : ℕ) {m : ℕ} (x : option α) (e : set (option α))

lemma try_until_zero : oa.try_until p 0 =
  (λ xs, (vector.to_list xs).find p) <$> (return vector.nil) := rfl

lemma try_until_succ : oa.try_until p n.succ =
  (λ xs, (vector.to_list xs).find p) <$> do {a ← oa, as ← oa.repeat n, return (a ::ᵥ as)} := rfl

/-- Any positive result of `oa.try_until p n` will be some output of `oa`. -/
lemma mem_support_of_some_mem_support_try_until (x : α)
  (hx : some x ∈ (oa.try_until p n).support) : x ∈ oa.support :=
begin
  simp_rw [try_until, support_map, set.mem_image, mem_support_repeat_iff_forall] at hx,
  exact let ⟨xs, hxs, hxs'⟩ := hx in hxs x (list.find_mem hxs')
end

/-- Any positive result of `oa.try_until p n` will satisfy the predicate `p`. -/
lemma pos_of_some_mem_support_try_until (x : α)
  (hx : some x ∈ (oa.try_until p n).support) : p x :=
begin
  simp_rw [try_until, support_map, set.mem_image, mem_support_repeat_iff_forall] at hx,
  exact let ⟨xs, hxs, hxs'⟩ := hx in list.find_some hxs'
end

section try_until_zero

/-- Running a computation zero times is distributionally equivalent to just returning failure. -/
@[simp, simp_dist_equiv] lemma try_until_zero_dist_equiv :
  oa.try_until p 0 ≃ₚ (return none : oracle_comp spec _) :=
by simp [dist_equiv_return_iff, try_until_zero]

/-- Running a computation zero times will never return a positive result. -/
@[simp] lemma support_try_until_zero : (oa.try_until p 0).support = {none} :=
(try_until_zero_dist_equiv oa p).support_eq.trans (support_return _ _)

lemma mem_support_try_until_zero_iff : x ∈ (oa.try_until p 0).support ↔ x = none :=
by rw [support_try_until_zero, set.mem_singleton_iff]

@[simp] lemma fin_support_try_until_zero : (oa.try_until p 0).fin_support = {none} :=
(try_until_zero_dist_equiv oa p).fin_support_eq.trans (fin_support_return _ _)

lemma mem_fin_support_try_until_iff : x ∈ (oa.try_until p 0).fin_support ↔ x = none :=
by rw [fin_support_try_until_zero, finset.mem_singleton]

@[simp] lemma eval_dist_try_until_zero : ⁅oa.try_until p 0⁆ = pmf.pure none :=
(try_until_zero_dist_equiv oa p).eval_dist_eq.trans (eval_dist_return _)

lemma eval_dist_try_until_zero_apply : ⁅= x | oa.try_until p 0⁆ = x.rec_on 1 (λ _, 0) :=
((try_until_zero_dist_equiv oa p).eval_dist_apply_eq x).trans (by cases x; simp)

@[simp] lemma prob_event_try_until_zero_eq_indicator :
  ⁅e | oa.try_until p 0⁆ = e.indicator (λ _, 1) none :=
((try_until_zero_dist_equiv oa p).prob_event_eq e).trans (prob_event_return_eq_indicator spec _ e)

@[simp] lemma prob_event_try_until_zero [decidable_pred (∈ e)] :
  ⁅e | oa.try_until p 0⁆ = if none ∈ e then 1 else 0 :=
((try_until_zero_dist_equiv oa p).prob_event_eq e).trans (prob_event_return spec _ e)

end try_until_zero

section try_until_succ

lemma try_until_succ_dist_equiv : oa.try_until p n.succ ≃ₚ
  do {x ← oa, if p x then return (some x) else oa.try_until p n} :=
-- calc oa.try_until p n.succ ≃ₚ (λ xs, (vector.to_list xs).find p) <$> (repeat oa n)

begin
  rw [try_until_succ],
  refine (map_bind_dist_equiv _ _ _).trans _,
  pairwise_dist_equiv,
  refine (map_bind_dist_equiv _ _ _).trans _,

  rw [dist_equiv_ite_iff],
  refine ⟨λ hpx, _, λ hxp, _⟩,
  {
    sorry
  },
  {
    rw [try_until, map_eq_bind_return_comp],
    pairwise_dist_equiv,
    refine trans (map_return_dist_equiv _ _) _,
    rw [vector.to_list_cons, list.find_cons_of_neg _ hxp],
  }

  -- calc (λ xs, list.find p (vector.to_list xs)) <$> (oa.repeat n >>= λ xs, return (x ::ᵥ xs)) ≃ₚ
  --   oa.repeat n >>= λ xs, (λ xs, list.find p (vector.to_list xs)) <$> (return (x ::ᵥ xs)) :
  --     map_bind_dist_equiv _ _ _
  --   ... ≃ₚ oa.repeat n >>= λ xs, (if p x then return x else return (list.find p (vector.to_list xs))) :
  --     begin
  --       pairwise_dist_equiv,
  --       refine (map_return_dist_equiv _ _).trans _, sorry,
  --     end
  --   ... ≃ₚ ite (p x) (return (some x)) (oa.try_until p n) :
  --     by split_ifs with hpx; pairwise_dist_equiv
end

/-- `oa.try_until p n` can fail to find a result iff there's an output `x` of `oa` with `¬ p x`. -/
lemma none_mem_support_try_until_succ_iff :
  none ∈ (oa.try_until p n.succ).support ↔ ∃ x ∈ oa.support, ¬ p x :=
begin
  simp only [try_until, mem_support_map_iff, list.find_eq_none],
  exact ⟨λ h, let ⟨xs, hxs, hp⟩ := h in ⟨xs.head, mem_support_of_mem_of_support_repeat hxs
    xs.head_mem, hp _ xs.head_mem⟩, λ h,
  let ⟨x, hx, hp⟩ := h in ⟨vector.replicate n.succ x,
    replicate_mem_support_repeat n.succ hx, λ y hy, (list.eq_of_mem_replicate hy).symm ▸ hp⟩⟩
end

lemma none_mem_support_try_until_succ {x : α} (hx : x ∈ oa.support) (h : ¬ p x) :
  none ∈ (oa.try_until p n.succ).support :=
(none_mem_support_try_until_succ_iff oa p n).2 ⟨x, hx, h⟩

lemma none_not_mem_support_try_until_succ (hx : ∀ x ∈ oa.support, p x) :
  none ∉ (oa.try_until p n.succ).support :=
mt (none_mem_support_try_until_succ_iff oa p n).1 (by simpa only [not_exists, not_not] using hx)

/-- The possible successful results of `oa.try_until p n` are outputs `x` of `oa` with `p x`. -/
@[simp] lemma some_mem_support_try_until_succ_iff (x : α) :
  some x ∈ (oa.try_until p n.succ).support ↔ x ∈ oa.support ∧ p x :=
(mem_support_map_iff _ _ _).trans (⟨λ h, let ⟨xs, hxs, hp⟩ := h in
  ⟨mem_support_of_mem_of_support_repeat hxs (list.find_mem hp), list.find_some hp⟩, λ h,
    ⟨vector.replicate _ x, replicate_mem_support_repeat _ h.1, by simp [vector.replicate, h.2]⟩⟩)

lemma some_mem_support_try_until_succ {x : α} (hx : x ∈ oa.support) (h : p x) :
  some x ∈ (oa.try_until p n.succ).support :=
(some_mem_support_try_until_succ_iff oa p n x).2 ⟨hx, h⟩

lemma some_not_mem_support_try_until_succ {x : α} (hx : x ∈ oa.support) (h : ¬ p x) :
  some x ∉ (oa.try_until p n.succ).support :=
λ h', false.elim (h ((some_mem_support_try_until_succ_iff _ _ _ _).1 h').2)

-- lemma eval_dist_try_until_succ_apply (x : α) :
--   ⁅= x | oa.try_until p n.succ⁆ = ⁅= x | oa⁆

end try_until_succ

/-- If at least one result of `oa` doesn't satisfy `p` then the result of `oa.try_until p n.succ`
is either `none` (in the case of failure) or `some x` for some output `x` of `oa` with `p x`. -/
lemma support_try_until_succ_of_exists_neg (h : ∃ x ∈ oa.support, ¬ p x) :
  (oa.try_until p n.succ).support = insert none (option.some '' {x | x ∈ oa.support ∧ p x}) :=
begin
  obtain ⟨x, hx, hpx⟩ := h,
  refine set.ext (λ y, _),
  rw [try_until, support_map, support_repeat_eq_forall],
  cases y with y,
  { simp only [set.mem_image, set.mem_set_of_eq, list.find_eq_none, set.mem_insert_iff,
      eq_self_iff_true, and_false, exists_false, or_false, iff_true],
    refine ⟨vector.replicate n.succ x, λ y hy, _, λ y hy, _⟩;
    { sorry
      } },
  { simp only [set.mem_image, set.mem_set_of_eq, set.mem_insert_iff, exists_eq_right, false_or],
    refine ⟨λ h, let ⟨xs, hxs⟩ := h in ⟨hxs.1 _ (list.find_mem hxs.2), list.find_some hxs.2⟩,
    λ h, ⟨vector.replicate n.succ y, λ z hz, _, list.find_cons_of_pos _ h.2⟩⟩,
    sorry,
    -- rw [vector.repeat, vector.to_list, list.mem_repeat_succ_iff] at hz,
    -- exact hz.symm ▸ h.1
    }
end

/-- If all results of `oa` satisfy `p`, then `oa.try_until p n.succ` will just return `some x`,
for some `x ∈ oa.support`(in particular the result of the first of the `n.succ` runs). -/
lemma support_try_until_succ_of_forall_pos (hp : ∀ x ∈ oa.support, p x) :
  (oa.try_until p n.succ).support = option.some '' oa.support :=
begin
  refine set.ext (λ y, ⟨λ h, _, λ h, _⟩),
  { cases y with y,
    { exact false.elim (none_not_mem_support_try_until_succ oa p n hp h) },
    { exact ⟨y, mem_support_of_some_mem_support_try_until oa p _ y h, rfl⟩ } },
  { exact let ⟨x, hx⟩ := h in hx.2 ▸ some_mem_support_try_until_succ oa p _ hx.1 (hp x hx.1) }
end

section try_until_none

/-- The probability of `oa.try_until p n` failing to generate a result is the probability
of getting an output of `oa` not satisfying `p`, raised to the `n`th power. -/
lemma eval_dist_try_until_apply_none : ⁅= none | oa.try_until p n⁆ = (1 - ⁅p | oa⁆) ^ n :=
begin
  induction n with n hn,
  { rw [pow_zero, eval_dist_try_until_zero_apply] },
  { refine ((try_until_succ_dist_equiv _ _ n).eval_dist_apply_eq none).trans _,
    simp only [eval_dist_bind_ite_const_right, hn, ← pow_succ, eval_dist_return, pmf.pure_apply,
      if_false, mul_zero, if_t_t, tsum_zero, zero_add] }
end

end try_until_none


end oracle_comp